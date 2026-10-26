import V185TrunkScan23Chunk0124

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_740028 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_740028 : Nat := 118140960795 + 740028 * 2 ^ 59
def prefixEnd_740028 : Nat := 4983230072969 + 3 ^ 40 * 740028 * 2
def baseEnd_740028 : Nat := 379990061785535870746679

theorem tailTrace_740028 : CollatzResearch.WordTrace tailWord_740028 prefixEnd_740028 379990061785535870746679 := by
  unfold tailWord_740028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13495519281506208782674369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17994025708674945043565825 13495519281506208782674369)
  ·
    refine ⟨10121639461129656587005777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13495519281506208782674369 10121639461129656587005777)
    ·
      refine ⟨7591229595847242440254333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10121639461129656587005777 7591229595847242440254333)
      ·
        refine ⟨2846711098442715915095375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7591229595847242440254333 2846711098442715915095375)
        ·
          refine ⟨4270066647664073872643063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846711098442715915095375 4270066647664073872643063)
          ·
            refine ⟨6405099971496110808964595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270066647664073872643063 6405099971496110808964595)
            ·
              refine ⟨9607649957244166213446893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405099971496110808964595 9607649957244166213446893)
              ·
                refine ⟨3602868733966562330042585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9607649957244166213446893 3602868733966562330042585)
                ·
                  refine ⟨2702151550474921747531939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3602868733966562330042585 2702151550474921747531939)
                  ·
                    refine ⟨4053227325712382621297909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702151550474921747531939 4053227325712382621297909)
                    ·
                      refine ⟨379990061785535870746679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4053227325712382621297909 379990061785535870746679)
                      ·
                        rfl

theorem cell23_740028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_740028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740028 prefixEnd_740028 := by exact prefixLift 740028
  have htrace : WordTrace (prefixWord ++ tailWord_740028) baseStart_740028 baseEnd_740028 := by
    simpa [prefixWord, tailWord_740028, baseEnd_740028] using wordTrace_append hprefix tailTrace_740028
  have hstable : (prefixWord ++ tailWord_740028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740028).length < 2 ^ (prefixWord ++ tailWord_740028).sum := by decide
  have hdescent : baseEnd_740028 < baseStart_740028 := by decide
  rcases family_descends (prefixWord ++ tailWord_740028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740029 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_740029 : Nat := 118140960795 + 740029 * 2 ^ 59
def prefixEnd_740029 : Nat := 4983230072969 + 3 ^ 40 * 740029 * 2
def baseEnd_740029 : Nat := 379990575266190366834175

theorem tailTrace_740029 : CollatzResearch.WordTrace tailWord_740029 prefixEnd_740029 379990575266190366834175 := by
  unfold tailWord_740029
  simp only [CollatzResearch.WordTrace]
  refine ⟨26991075036008794736135141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17994050024005863157423427 26991075036008794736135141)
  ·
    refine ⟨5060826569251649013025339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26991075036008794736135141 5060826569251649013025339)
    ·
      refine ⟨7591239853877473519538009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5060826569251649013025339 7591239853877473519538009)
      ·
        refine ⟨5693429890408105139653507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7591239853877473519538009 5693429890408105139653507)
        ·
          refine ⟨8540144835612157709480261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693429890408105139653507 8540144835612157709480261)
          ·
            refine ⟨1601277156677279570527549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8540144835612157709480261 1601277156677279570527549)
            ·
              refine ⟨600478933753979838947831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1601277156677279570527549 600478933753979838947831)
              ·
                refine ⟨900718400630969758421747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600478933753979838947831 900718400630969758421747)
                ·
                  refine ⟨1351077600946454637632621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900718400630969758421747 1351077600946454637632621)
                  ·
                    refine ⟨506654100354920489112233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351077600946454637632621 506654100354920489112233)
                    ·
                      refine ⟨379990575266190366834175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506654100354920489112233 379990575266190366834175)
                      ·
                        rfl

theorem cell23_740029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_740029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740029 prefixEnd_740029 := by exact prefixLift 740029
  have htrace : WordTrace (prefixWord ++ tailWord_740029) baseStart_740029 baseEnd_740029 := by
    simpa [prefixWord, tailWord_740029, baseEnd_740029] using wordTrace_append hprefix tailTrace_740029
  have hstable : (prefixWord ++ tailWord_740029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740029).length < 2 ^ (prefixWord ++ tailWord_740029).sum := by decide
  have hdescent : baseEnd_740029 < baseStart_740029 := by decide
  rcases family_descends (prefixWord ++ tailWord_740029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740051 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 6]
def baseStart_740051 : Nat := 118140960795 + 740051 * 2 ^ 59
def prefixEnd_740051 : Nat := 4983230072969 + 3 ^ 40 * 740051 * 2
def baseEnd_740051 : Nat := 380001871840589280759073

theorem tailTrace_740051 : CollatzResearch.WordTrace tailWord_740051 prefixEnd_740051 380001871840589280759073 := by
  unfold tailWord_740051
  simp only [CollatzResearch.WordTrace]
  refine ⟨26991877441929092493436007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17994584961286061662290671 26991877441929092493436007)
  ·
    refine ⟨40487816162893638740154011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26991877441929092493436007 40487816162893638740154011)
    ·
      refine ⟨60731724244340458110231017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40487816162893638740154011 60731724244340458110231017)
      ·
        refine ⟨45548793183255343582673263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60731724244340458110231017 45548793183255343582673263)
        ·
          refine ⟨68323189774883015374009895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45548793183255343582673263 68323189774883015374009895)
          ·
            refine ⟨102484784662324523061014843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68323189774883015374009895 102484784662324523061014843)
            ·
              refine ⟨153727176993486784591522265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102484784662324523061014843 153727176993486784591522265)
              ·
                refine ⟨115295382745115088443641699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153727176993486784591522265 115295382745115088443641699)
                ·
                  refine ⟨172943074117672632665462549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115295382745115088443641699 172943074117672632665462549)
                  ·
                    refine ⟨8106706599265904656193557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 172943074117672632665462549 8106706599265904656193557)
                    ·
                      refine ⟨380001871840589280759073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8106706599265904656193557 380001871840589280759073)
                      ·
                        rfl

theorem cell23_740051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_740051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740051 prefixEnd_740051 := by exact prefixLift 740051
  have htrace : WordTrace (prefixWord ++ tailWord_740051) baseStart_740051 baseEnd_740051 := by
    simpa [prefixWord, tailWord_740051, baseEnd_740051] using wordTrace_append hprefix tailTrace_740051
  have hstable : (prefixWord ++ tailWord_740051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740051).length < 2 ^ (prefixWord ++ tailWord_740051).sum := by decide
  have hdescent : baseEnd_740051 < baseStart_740051 := by decide
  rcases family_descends (prefixWord ++ tailWord_740051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740082 : List Nat := [3, 2, 1, 3, 1, 3, 2, 3, 5]
def baseStart_740082 : Nat := 118140960795 + 740082 * 2 ^ 59
def prefixEnd_740082 : Nat := 4983230072969 + 3 ^ 40 * 740082 * 2
def baseEnd_740082 : Nat := 42224198860097628830159

theorem tailTrace_740082 : CollatzResearch.WordTrace tailWord_740082 prefixEnd_740082 42224198860097628830159 := by
  unfold tailWord_740082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748252026204196196953625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17995338736544523191876333 6748252026204196196953625)
  ·
    refine ⟨5061189019653147147715219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6748252026204196196953625 5061189019653147147715219)
    ·
      refine ⟨7591783529479720721572829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5061189019653147147715219 7591783529479720721572829)
      ·
        refine ⟨2846918823554895270589811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7591783529479720721572829 2846918823554895270589811)
        ·
          refine ⟨4270378235332342905884717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846918823554895270589811 4270378235332342905884717)
          ·
            refine ⟨1601391838249628589706769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4270378235332342905884717 1601391838249628589706769)
            ·
              refine ⟨1201043878687221442280077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601391838249628589706769 1201043878687221442280077)
              ·
                refine ⟨450391454507708040855029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1201043878687221442280077 450391454507708040855029)
                ·
                  refine ⟨42224198860097628830159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 450391454507708040855029 42224198860097628830159)
                  ·
                    rfl

theorem cell23_740082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_740082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740082 prefixEnd_740082 := by exact prefixLift 740082
  have htrace : WordTrace (prefixWord ++ tailWord_740082) baseStart_740082 baseEnd_740082 := by
    simpa [prefixWord, tailWord_740082, baseEnd_740082] using wordTrace_append hprefix tailTrace_740082
  have hstable : (prefixWord ++ tailWord_740082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740082).length < 2 ^ (prefixWord ++ tailWord_740082).sum := by decide
  have hdescent : baseEnd_740082 < baseStart_740082 := by decide
  rcases family_descends (prefixWord ++ tailWord_740082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740115 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 2, 4, 2]
def baseStart_740115 : Nat := 118140960795 + 740115 * 2 ^ 59
def prefixEnd_740115 : Nat := 4983230072969 + 3 ^ 40 * 740115 * 2
def baseEnd_740115 : Nat := 380034734602477030358779

theorem tailTrace_740115 : CollatzResearch.WordTrace tailWord_740115 prefixEnd_740115 380034734602477030358779 := by
  unfold tailWord_740115
  simp only [CollatzResearch.WordTrace]
  refine ⟨26994211713697231423765799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17996141142464820949177199 26994211713697231423765799)
  ·
    refine ⟨40491317570545847135648699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26994211713697231423765799 40491317570545847135648699)
    ·
      refine ⟨60736976355818770703473049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40491317570545847135648699 60736976355818770703473049)
      ·
        refine ⟨45552732266864078027604787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60736976355818770703473049 45552732266864078027604787)
        ·
          refine ⟨68329098400296117041407181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45552732266864078027604787 68329098400296117041407181)
          ·
            refine ⟨25623411900111043890527693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68329098400296117041407181 25623411900111043890527693)
            ·
              refine ⟨9608779462541641458947885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25623411900111043890527693 9608779462541641458947885)
              ·
                refine ⟨3603292298453115547105457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9608779462541641458947885 3603292298453115547105457)
                ·
                  refine ⟨2702469223839836660329093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3603292298453115547105457 2702469223839836660329093)
                  ·
                    refine ⟨506712979469969373811705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2702469223839836660329093 506712979469969373811705)
                    ·
                      refine ⟨380034734602477030358779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506712979469969373811705 380034734602477030358779)
                      ·
                        rfl

theorem cell23_740115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 4, 2].length) (baseStart_740115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740115 prefixEnd_740115 := by exact prefixLift 740115
  have htrace : WordTrace (prefixWord ++ tailWord_740115) baseStart_740115 baseEnd_740115 := by
    simpa [prefixWord, tailWord_740115, baseEnd_740115] using wordTrace_append hprefix tailTrace_740115
  have hstable : (prefixWord ++ tailWord_740115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740115).length < 2 ^ (prefixWord ++ tailWord_740115).sum := by decide
  have hdescent : baseEnd_740115 < baseStart_740115 := by decide
  rcases family_descends (prefixWord ++ tailWord_740115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740172 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 6]
def baseStart_740172 : Nat := 118140960795 + 740172 * 2 ^ 59
def prefixEnd_740172 : Nat := 4983230072969 + 3 ^ 40 * 740172 * 2
def baseEnd_740172 : Nat := 42229333666642589705113

theorem tailTrace_740172 : CollatzResearch.WordTrace tailWord_740172 prefixEnd_740172 42229333666642589705113 := by
  unfold tailWord_740172
  simp only [CollatzResearch.WordTrace]
  refine ⟨13498145337245365079295385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17997527116327153439060513 13498145337245365079295385)
  ·
    refine ⟨10123609002934023809471539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13498145337245365079295385 10123609002934023809471539)
    ·
      refine ⟨15185413504401035714207309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10123609002934023809471539 15185413504401035714207309)
      ·
        refine ⟨5694530064150388392827741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15185413504401035714207309 5694530064150388392827741)
        ·
          refine ⟨2135448774056395647310403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5694530064150388392827741 2135448774056395647310403)
          ·
            refine ⟨3203173161084593470965605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135448774056395647310403 3203173161084593470965605)
            ·
              refine ⟨600594967703361275806051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3203173161084593470965605 600594967703361275806051)
              ·
                refine ⟨900892451555041913709077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600594967703361275806051 900892451555041913709077)
                ·
                  refine ⟨42229333666642589705113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 900892451555041913709077 42229333666642589705113)
                  ·
                    rfl

theorem cell23_740172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_740172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740172 prefixEnd_740172 := by exact prefixLift 740172
  have htrace : WordTrace (prefixWord ++ tailWord_740172) baseStart_740172 baseEnd_740172 := by
    simpa [prefixWord, tailWord_740172, baseEnd_740172] using wordTrace_append hprefix tailTrace_740172
  have hstable : (prefixWord ++ tailWord_740172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740172).length < 2 ^ (prefixWord ++ tailWord_740172).sum := by decide
  have hdescent : baseEnd_740172 < baseStart_740172 := by decide
  rcases family_descends (prefixWord ++ tailWord_740172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740185 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 3, 5]
def baseStart_740185 : Nat := 118140960795 + 740185 * 2 ^ 59
def prefixEnd_740185 : Nat := 4983230072969 + 3 ^ 40 * 740185 * 2
def baseEnd_740185 : Nat := 126690226082763918827819

theorem tailTrace_740185 : CollatzResearch.WordTrace tailWord_740185 prefixEnd_740185 126690226082763918827819 := by
  unfold tailWord_740185
  simp only [CollatzResearch.WordTrace]
  refine ⟨26996764823443633378814009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17997843215629088919209339 26996764823443633378814009)
  ·
    refine ⟨20247573617582725034110507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26996764823443633378814009 20247573617582725034110507)
    ·
      refine ⟨30371360426374087551165761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20247573617582725034110507 30371360426374087551165761)
      ·
        refine ⟨22778520319780565663374321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30371360426374087551165761 22778520319780565663374321)
        ·
          refine ⟨17083890239835424247530741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22778520319780565663374321 17083890239835424247530741)
          ·
            refine ⟨1601614709984571023206007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17083890239835424247530741 1601614709984571023206007)
            ·
              refine ⟨2402422064976856534809011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601614709984571023206007 2402422064976856534809011)
              ·
                refine ⟨3603633097465284802213517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402422064976856534809011 3603633097465284802213517)
                ·
                  refine ⟨1351362411549481800830069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3603633097465284802213517 1351362411549481800830069)
                  ·
                    refine ⟨126690226082763918827819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1351362411549481800830069 126690226082763918827819)
                    ·
                      rfl

theorem cell23_740185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_740185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740185 prefixEnd_740185 := by exact prefixLift 740185
  have htrace : WordTrace (prefixWord ++ tailWord_740185) baseStart_740185 baseEnd_740185 := by
    simpa [prefixWord, tailWord_740185, baseEnd_740185] using wordTrace_append hprefix tailTrace_740185
  have hstable : (prefixWord ++ tailWord_740185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740185).length < 2 ^ (prefixWord ++ tailWord_740185).sum := by decide
  have hdescent : baseEnd_740185 < baseStart_740185 := by decide
  rcases family_descends (prefixWord ++ tailWord_740185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740215 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 4, 4]
def baseStart_740215 : Nat := 118140960795 + 740215 * 2 ^ 59
def prefixEnd_740215 : Nat := 4983230072969 + 3 ^ 40 * 740215 * 2
def baseEnd_740215 : Nat := 126695360889308879702773

theorem tailTrace_740215 : CollatzResearch.WordTrace tailWord_740215 prefixEnd_740215 126695360889308879702773 := by
  unfold tailWord_740215
  simp only [CollatzResearch.WordTrace]
  refine ⟨26997859013334948502406099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17998572675556632334937399 26997859013334948502406099)
  ·
    refine ⟨40496788520002422753609149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26997859013334948502406099 40496788520002422753609149)
    ·
      refine ⟨15186295695000908532603431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40496788520002422753609149 15186295695000908532603431)
      ·
        refine ⟨22779443542501362798905147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15186295695000908532603431 22779443542501362798905147)
        ·
          refine ⟨34169165313752044198357721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22779443542501362798905147 34169165313752044198357721)
          ·
            refine ⟨25626873985314033148768291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34169165313752044198357721 25626873985314033148768291)
            ·
              refine ⟨38440310977971049723152437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25626873985314033148768291 38440310977971049723152437)
              ·
                refine ⟨3603779154184785911545541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38440310977971049723152437 3603779154184785911545541)
                ·
                  refine ⟨675708591409647358414789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3603779154184785911545541 675708591409647358414789)
                  ·
                    refine ⟨126695360889308879702773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675708591409647358414789 126695360889308879702773)
                    ·
                      rfl

theorem cell23_740215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_740215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740215 prefixEnd_740215 := by exact prefixLift 740215
  have htrace : WordTrace (prefixWord ++ tailWord_740215) baseStart_740215 baseEnd_740215 := by
    simpa [prefixWord, tailWord_740215, baseEnd_740215] using wordTrace_append hprefix tailTrace_740215
  have hstable : (prefixWord ++ tailWord_740215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740215).length < 2 ^ (prefixWord ++ tailWord_740215).sum := by decide
  have hdescent : baseEnd_740215 < baseStart_740215 := by decide
  rcases family_descends (prefixWord ++ tailWord_740215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740232 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 1, 6]
def baseStart_740232 : Nat := 118140960795 + 740232 * 2 ^ 59
def prefixEnd_740232 : Nat := 4983230072969 + 3 ^ 40 * 740232 * 2
def baseEnd_740232 : Nat := 126698270613017690865247

theorem tailTrace_740232 : CollatzResearch.WordTrace tailWord_740232 prefixEnd_740232 126698270613017690865247 := by
  unfold tailWord_740232
  simp only [CollatzResearch.WordTrace]
  refine ⟨13499239527136680202887475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17998986036182240270516633 13499239527136680202887475)
  ·
    refine ⟨20248859290705020304331213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13499239527136680202887475 20248859290705020304331213)
    ·
      refine ⟨7593322234014382614124205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20248859290705020304331213 7593322234014382614124205)
      ·
        refine ⟨2847495837755393480296577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7593322234014382614124205 2847495837755393480296577)
        ·
          refine ⟨2135621878316545110222433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2847495837755393480296577 2135621878316545110222433)
          ·
            refine ⟨1601716408737408832666825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135621878316545110222433 1601716408737408832666825)
            ·
              refine ⟨1201287306553056624500119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601716408737408832666825 1201287306553056624500119)
              ·
                refine ⟨1801930959829584936750179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201287306553056624500119 1801930959829584936750179)
                ·
                  refine ⟨2702896439744377405125269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801930959829584936750179 2702896439744377405125269)
                  ·
                    refine ⟨126698270613017690865247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2702896439744377405125269 126698270613017690865247)
                    ·
                      rfl

theorem cell23_740232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_740232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740232 prefixEnd_740232 := by exact prefixLift 740232
  have htrace : WordTrace (prefixWord ++ tailWord_740232) baseStart_740232 baseEnd_740232 := by
    simpa [prefixWord, tailWord_740232, baseEnd_740232] using wordTrace_append hprefix tailTrace_740232
  have hstable : (prefixWord ++ tailWord_740232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740232).length < 2 ^ (prefixWord ++ tailWord_740232).sum := by decide
  have hdescent : baseEnd_740232 < baseStart_740232 := by decide
  rcases family_descends (prefixWord ++ tailWord_740232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740235 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 4]
def baseStart_740235 : Nat := 118140960795 + 740235 * 2 ^ 59
def prefixEnd_740235 : Nat := 4983230072969 + 3 ^ 40 * 740235 * 2
def baseEnd_740235 : Nat := 380096352281016560858227

theorem tailTrace_740235 : CollatzResearch.WordTrace tailWord_740235 prefixEnd_740235 380096352281016560858227 := by
  unfold tailWord_740235
  simp only [CollatzResearch.WordTrace]
  refine ⟨26998588473262491918134159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17999058982174994612089439 26998588473262491918134159)
  ·
    refine ⟨40497882709893737877201239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26998588473262491918134159 40497882709893737877201239)
    ·
      refine ⟨60746824064840606815801859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40497882709893737877201239 60746824064840606815801859)
      ·
        refine ⟨91120236097260910223702789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60746824064840606815801859 91120236097260910223702789)
        ·
          refine ⟨17085044268236420666944273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91120236097260910223702789 17085044268236420666944273)
          ·
            refine ⟨12813783201177315500208205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17085044268236420666944273 12813783201177315500208205)
            ·
              refine ⟨4805168700441493312578077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12813783201177315500208205 4805168700441493312578077)
              ·
                refine ⟨1801938262665559992216779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4805168700441493312578077 1801938262665559992216779)
                ·
                  refine ⟨2702907393998339988325169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801938262665559992216779 2702907393998339988325169)
                  ·
                    refine ⟨2027180545498754991243877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2702907393998339988325169 2027180545498754991243877)
                    ·
                      refine ⟨380096352281016560858227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2027180545498754991243877 380096352281016560858227)
                      ·
                        rfl

theorem cell23_740235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 4].length) (baseStart_740235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740235 prefixEnd_740235 := by exact prefixLift 740235
  have htrace : WordTrace (prefixWord ++ tailWord_740235) baseStart_740235 baseEnd_740235 := by
    simpa [prefixWord, tailWord_740235, baseEnd_740235] using wordTrace_append hprefix tailTrace_740235
  have hstable : (prefixWord ++ tailWord_740235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740235).length < 2 ^ (prefixWord ++ tailWord_740235).sum := by decide
  have hdescent : baseEnd_740235 < baseStart_740235 := by decide
  rcases family_descends (prefixWord ++ tailWord_740235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740256 : List Nat := [2, 1, 1, 4, 1, 1, 3, 5, 1, 2, 2]
def baseStart_740256 : Nat := 118140960795 + 740256 * 2 ^ 59
def prefixEnd_740256 : Nat := 4983230072969 + 3 ^ 40 * 740256 * 2
def baseEnd_740256 : Nat := 380107135374760978695631

theorem tailTrace_740256 : CollatzResearch.WordTrace tailWord_740256 prefixEnd_740256 380107135374760978695631 := by
  unfold tailWord_740256
  simp only [CollatzResearch.WordTrace]
  refine ⟨13499677203093206252324311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17999569604124275003099081 13499677203093206252324311)
  ·
    refine ⟨20249515804639809378486467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13499677203093206252324311 20249515804639809378486467)
    ·
      refine ⟨30374273706959714067729701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20249515804639809378486467 30374273706959714067729701)
      ·
        refine ⟨5695176320054946387699319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30374273706959714067729701 5695176320054946387699319)
        ·
          refine ⟨8542764480082419581548979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695176320054946387699319 8542764480082419581548979)
          ·
            refine ⟨12814146720123629372323469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8542764480082419581548979 12814146720123629372323469)
            ·
              refine ⟨4805305020046361014621301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12814146720123629372323469 4805305020046361014621301)
              ·
                refine ⟨450497345629346345120747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4805305020046361014621301 450497345629346345120747)
                ·
                  refine ⟨675746018444019517681121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450497345629346345120747 675746018444019517681121)
                  ·
                    refine ⟨506809513833014638260841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 675746018444019517681121 506809513833014638260841)
                    ·
                      refine ⟨380107135374760978695631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506809513833014638260841 380107135374760978695631)
                      ·
                        rfl

theorem cell23_740256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_740256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740256 prefixEnd_740256 := by exact prefixLift 740256
  have htrace : WordTrace (prefixWord ++ tailWord_740256) baseStart_740256 baseEnd_740256 := by
    simpa [prefixWord, tailWord_740256, baseEnd_740256] using wordTrace_append hprefix tailTrace_740256
  have hstable : (prefixWord ++ tailWord_740256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740256).length < 2 ^ (prefixWord ++ tailWord_740256).sum := by decide
  have hdescent : baseEnd_740256 < baseStart_740256 := by decide
  rcases family_descends (prefixWord ++ tailWord_740256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740259 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 1, 2, 3]
def baseStart_740259 : Nat := 118140960795 + 740259 * 2 ^ 59
def prefixEnd_740259 : Nat := 4983230072969 + 3 ^ 40 * 740259 * 2
def baseEnd_740259 : Nat := 380108675816724466958117

theorem tailTrace_740259 : CollatzResearch.WordTrace tailWord_740259 prefixEnd_740259 380108675816724466958117 := by
  unfold tailWord_740259
  simp only [CollatzResearch.WordTrace]
  refine ⟨26999463825175544017007831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17999642550117029344671887 26999463825175544017007831)
  ·
    refine ⟨40499195737763316025511747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26999463825175544017007831 40499195737763316025511747)
    ·
      refine ⟨60748793606644974038267621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40499195737763316025511747 60748793606644974038267621)
      ·
        refine ⟨11390398801245932632175179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60748793606644974038267621 11390398801245932632175179)
        ·
          refine ⟨17085598201868898948262769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11390398801245932632175179 17085598201868898948262769)
          ·
            refine ⟨12814198651401674211197077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17085598201868898948262769 12814198651401674211197077)
            ·
              refine ⟨600665561784453478649863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12814198651401674211197077 600665561784453478649863)
              ·
                refine ⟨900998342676680217974795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600665561784453478649863 900998342676680217974795)
                ·
                  refine ⟨1351497514015020326962193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900998342676680217974795 1351497514015020326962193)
                  ·
                    refine ⟨1013623135511265245221645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1351497514015020326962193 1013623135511265245221645)
                    ·
                      refine ⟨380108675816724466958117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1013623135511265245221645 380108675816724466958117)
                      ·
                        rfl

theorem cell23_740259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_740259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740259 prefixEnd_740259 := by exact prefixLift 740259
  have htrace : WordTrace (prefixWord ++ tailWord_740259) baseStart_740259 baseEnd_740259 := by
    simpa [prefixWord, tailWord_740259, baseEnd_740259] using wordTrace_append hprefix tailTrace_740259
  have hstable : (prefixWord ++ tailWord_740259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740259).length < 2 ^ (prefixWord ++ tailWord_740259).sum := by decide
  have hdescent : baseEnd_740259 < baseStart_740259 := by decide
  rcases family_descends (prefixWord ++ tailWord_740259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740295 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_740295 : Nat := 118140960795 + 740295 * 2 ^ 59
def prefixEnd_740295 : Nat := 4983230072969 + 3 ^ 40 * 740295 * 2
def baseEnd_740295 : Nat := 380127161120286326107951

theorem tailTrace_740295 : CollatzResearch.WordTrace tailWord_740295 prefixEnd_740295 380127161120286326107951 := by
  unfold tailWord_740295
  simp only [CollatzResearch.WordTrace]
  refine ⟨27000776853045122165318339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18000517902030081443545559 27000776853045122165318339)
  ·
    refine ⟨40501165279567683247977509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27000776853045122165318339 40501165279567683247977509)
    ·
      refine ⟨7593968489918940608995783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40501165279567683247977509 7593968489918940608995783)
      ·
        refine ⟨11390952734878410913493675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7593968489918940608995783 11390952734878410913493675)
        ·
          refine ⟨17086429102317616370240513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11390952734878410913493675 17086429102317616370240513)
          ·
            refine ⟨12814821826738212277680385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17086429102317616370240513 12814821826738212277680385)
            ·
              refine ⟨9611116370053659208260289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12814821826738212277680385 9611116370053659208260289)
              ·
                refine ⟨7208337277540244406195217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9611116370053659208260289 7208337277540244406195217)
                ·
                  refine ⟨5406252958155183304646413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208337277540244406195217 5406252958155183304646413)
                  ·
                    refine ⟨2027344859308193739242405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5406252958155183304646413 2027344859308193739242405)
                    ·
                      refine ⟨380127161120286326107951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2027344859308193739242405 380127161120286326107951)
                      ·
                        rfl

theorem cell23_740295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_740295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740295 prefixEnd_740295 := by exact prefixLift 740295
  have htrace : WordTrace (prefixWord ++ tailWord_740295) baseStart_740295 baseEnd_740295 := by
    simpa [prefixWord, tailWord_740295, baseEnd_740295] using wordTrace_append hprefix tailTrace_740295
  have hstable : (prefixWord ++ tailWord_740295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740295).length < 2 ^ (prefixWord ++ tailWord_740295).sum := by decide
  have hdescent : baseEnd_740295 < baseStart_740295 := by decide
  rcases family_descends (prefixWord ++ tailWord_740295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740299 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 1, 3, 2]
def baseStart_740299 : Nat := 118140960795 + 740299 * 2 ^ 59
def prefixEnd_740299 : Nat := 4983230072969 + 3 ^ 40 * 740299 * 2
def baseEnd_740299 : Nat := 380129215042904310457933

theorem tailTrace_740299 : CollatzResearch.WordTrace tailWord_740299 prefixEnd_740299 380129215042904310457933 := by
  unfold tailWord_740299
  simp only [CollatzResearch.WordTrace]
  refine ⟨27000922745030630848463951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18000615163353753898975967 27000922745030630848463951)
  ·
    refine ⟨40501384117545946272695927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27000922745030630848463951 40501384117545946272695927)
    ·
      refine ⟨60752076176318919409043891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40501384117545946272695927 60752076176318919409043891)
      ·
        refine ⟨91128114264478379113565837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60752076176318919409043891 91128114264478379113565837)
        ·
          refine ⟨34173042849179392167587189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91128114264478379113565837 34173042849179392167587189)
          ·
            refine ⟨3203722767110568015711299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34173042849179392167587189 3203722767110568015711299)
            ·
              refine ⟨4805584150665852023566949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203722767110568015711299 4805584150665852023566949)
              ·
                refine ⟨901047028249847254418803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4805584150665852023566949 901047028249847254418803)
                ·
                  refine ⟨1351570542374770881628205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901047028249847254418803 1351570542374770881628205)
                  ·
                    refine ⟨506838953390539080610577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351570542374770881628205 506838953390539080610577)
                    ·
                      refine ⟨380129215042904310457933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506838953390539080610577 380129215042904310457933)
                      ·
                        rfl

theorem cell23_740299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 3, 2].length) (baseStart_740299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740299 prefixEnd_740299 := by exact prefixLift 740299
  have htrace : WordTrace (prefixWord ++ tailWord_740299) baseStart_740299 baseEnd_740299 := by
    simpa [prefixWord, tailWord_740299, baseEnd_740299] using wordTrace_append hprefix tailTrace_740299
  have hstable : (prefixWord ++ tailWord_740299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740299).length < 2 ^ (prefixWord ++ tailWord_740299).sum := by decide
  have hdescent : baseEnd_740299 < baseStart_740299 := by decide
  rcases family_descends (prefixWord ++ tailWord_740299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740350 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_740350 : Nat := 118140960795 + 740350 * 2 ^ 59
def prefixEnd_740350 : Nat := 4983230072969 + 3 ^ 40 * 740350 * 2
def baseEnd_740350 : Nat := 380155402556283610920199

theorem tailTrace_740350 : CollatzResearch.WordTrace tailWord_740350 prefixEnd_740350 380155402556283610920199 := by
  unfold tailWord_740350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375347858480733319821313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18001855245230577705713669 3375347858480733319821313)
  ·
    refine ⟨2531510893860549989865985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3375347858480733319821313 2531510893860549989865985)
    ·
      refine ⟨1898633170395412492399489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2531510893860549989865985 1898633170395412492399489)
      ·
        refine ⟨1423974877796559369299617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1898633170395412492399489 1423974877796559369299617)
        ·
          refine ⟨1067981158347419526974713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423974877796559369299617 1067981158347419526974713)
          ·
            refine ⟨800985868760564645231035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1067981158347419526974713 800985868760564645231035)
            ·
              refine ⟨1201478803140846967846553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800985868760564645231035 1201478803140846967846553)
              ·
                refine ⟨901109102355635225884915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201478803140846967846553 901109102355635225884915)
                ·
                  refine ⟨1351663653533452838827373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901109102355635225884915 1351663653533452838827373)
                  ·
                    refine ⟨506873870075044814560265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351663653533452838827373 506873870075044814560265)
                    ·
                      refine ⟨380155402556283610920199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506873870075044814560265 380155402556283610920199)
                      ·
                        rfl

theorem cell23_740350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_740350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740350 prefixEnd_740350 := by exact prefixLift 740350
  have htrace : WordTrace (prefixWord ++ tailWord_740350) baseStart_740350 baseEnd_740350 := by
    simpa [prefixWord, tailWord_740350, baseEnd_740350] using wordTrace_append hprefix tailTrace_740350
  have hstable : (prefixWord ++ tailWord_740350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740350).length < 2 ^ (prefixWord ++ tailWord_740350).sum := by decide
  have hdescent : baseEnd_740350 < baseStart_740350 := by decide
  rcases family_descends (prefixWord ++ tailWord_740350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740386 : List Nat := [3, 3, 1, 1, 1, 3, 4, 2, 5]
def baseStart_740386 : Nat := 118140960795 + 740386 * 2 ^ 59
def prefixEnd_740386 : Nat := 4983230072969 + 3 ^ 40 * 740386 * 2
def baseEnd_740386 : Nat := 42241543095538385563337

theorem tailTrace_740386 : CollatzResearch.WordTrace tailWord_740386 prefixEnd_740386 42241543095538385563337 := by
  unfold tailWord_740386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751023973928861176720253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18002730597143629804587341 6751023973928861176720253)
  ·
    refine ⟨2531633990223322941270095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6751023973928861176720253 2531633990223322941270095)
    ·
      refine ⟨3797450985334984411905143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531633990223322941270095 3797450985334984411905143)
      ·
        refine ⟨5696176478002476617857715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797450985334984411905143 5696176478002476617857715)
        ·
          refine ⟨8544264717003714926786573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5696176478002476617857715 8544264717003714926786573)
          ·
            refine ⟨3204099268876393097544965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8544264717003714926786573 3204099268876393097544965)
            ·
              refine ⟨600768612914323705789681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3204099268876393097544965 600768612914323705789681)
              ·
                refine ⟨450576459685742779342261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600768612914323705789681 450576459685742779342261)
                ·
                  refine ⟨42241543095538385563337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 450576459685742779342261 42241543095538385563337)
                  ·
                    rfl

theorem cell23_740386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_740386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740386 prefixEnd_740386 := by exact prefixLift 740386
  have htrace : WordTrace (prefixWord ++ tailWord_740386) baseStart_740386 baseEnd_740386 := by
    simpa [prefixWord, tailWord_740386, baseEnd_740386] using wordTrace_append hprefix tailTrace_740386
  have hstable : (prefixWord ++ tailWord_740386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740386).length < 2 ^ (prefixWord ++ tailWord_740386).sum := by decide
  have hdescent : baseEnd_740386 < baseStart_740386 := by decide
  rcases family_descends (prefixWord ++ tailWord_740386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740402 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_740402 : Nat := 118140960795 + 740402 * 2 ^ 59
def prefixEnd_740402 : Nat := 4983230072969 + 3 ^ 40 * 740402 * 2
def baseEnd_740402 : Nat := 380182103550317407469959

theorem tailTrace_740402 : CollatzResearch.WordTrace tailWord_740402 prefixEnd_740402 380182103550317407469959 := by
  unfold tailWord_740402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751169865914369859865865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18003119642438319626308973 6751169865914369859865865)
  ·
    refine ⟨5063377399435777394899399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6751169865914369859865865 5063377399435777394899399)
    ·
      refine ⟨7595066099153666092349099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063377399435777394899399 7595066099153666092349099)
      ·
        refine ⟨11392599148730499138523649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595066099153666092349099 11392599148730499138523649)
        ·
          refine ⟨8544449361547874353892737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11392599148730499138523649 8544449361547874353892737)
          ·
            refine ⟨6408337021160905765419553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8544449361547874353892737 6408337021160905765419553)
            ·
              refine ⟨4806252765870679324064665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408337021160905765419553 4806252765870679324064665)
              ·
                refine ⟨3604689574403009493048499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806252765870679324064665 3604689574403009493048499)
                ·
                  refine ⟨5407034361604514239572749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604689574403009493048499 5407034361604514239572749)
                  ·
                    refine ⟨2027637885601692839839781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5407034361604514239572749 2027637885601692839839781)
                    ·
                      refine ⟨380182103550317407469959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2027637885601692839839781 380182103550317407469959)
                      ·
                        rfl

theorem cell23_740402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_740402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740402 prefixEnd_740402 := by exact prefixLift 740402
  have htrace : WordTrace (prefixWord ++ tailWord_740402) baseStart_740402 baseEnd_740402 := by
    simpa [prefixWord, tailWord_740402, baseEnd_740402] using wordTrace_append hprefix tailTrace_740402
  have hstable : (prefixWord ++ tailWord_740402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740402).length < 2 ^ (prefixWord ++ tailWord_740402).sum := by decide
  have hdescent : baseEnd_740402 < baseStart_740402 := by decide
  rcases family_descends (prefixWord ++ tailWord_740402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740442 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 6]
def baseStart_740442 : Nat := 118140960795 + 740442 * 2 ^ 59
def prefixEnd_740442 : Nat := 4983230072969 + 3 ^ 40 * 740442 * 2
def baseEnd_740442 : Nat := 42244738086277472329975

theorem tailTrace_740442 : CollatzResearch.WordTrace tailWord_740442 prefixEnd_740442 42244738086277472329975 := by
  unfold tailWord_740442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751534595878141567729895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18004092255675044180613053 6751534595878141567729895)
  ·
    refine ⟨10127301893817212351594843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6751534595878141567729895 10127301893817212351594843)
    ·
      refine ⟨15190952840725818527392265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10127301893817212351594843 15190952840725818527392265)
      ·
        refine ⟨11393214630544363895544199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15190952840725818527392265 11393214630544363895544199)
        ·
          refine ⟨17089821945816545843316299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393214630544363895544199 17089821945816545843316299)
          ·
            refine ⟨25634732918724818764974449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17089821945816545843316299 25634732918724818764974449)
            ·
              refine ⟨19226049689043614073730837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25634732918724818764974449 19226049689043614073730837)
              ·
                refine ⟨901221079173919409706133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19226049689043614073730837 901221079173919409706133)
                ·
                  refine ⟨42244738086277472329975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 901221079173919409706133 42244738086277472329975)
                  ·
                    rfl

theorem cell23_740442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_740442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740442 prefixEnd_740442 := by exact prefixLift 740442
  have htrace : WordTrace (prefixWord ++ tailWord_740442) baseStart_740442 baseEnd_740442 := by
    simpa [prefixWord, tailWord_740442, baseEnd_740442] using wordTrace_append hprefix tailTrace_740442
  have hstable : (prefixWord ++ tailWord_740442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740442).length < 2 ^ (prefixWord ++ tailWord_740442).sum := by decide
  have hdescent : baseEnd_740442 < baseStart_740442 := by decide
  rcases family_descends (prefixWord ++ tailWord_740442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740472 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 3, 5]
def baseStart_740472 : Nat := 118140960795 + 740472 * 2 ^ 59
def prefixEnd_740472 : Nat := 4983230072969 + 3 ^ 40 * 740472 * 2
def baseEnd_740472 : Nat := 126739349065377377864879

theorem tailTrace_740472 : CollatzResearch.WordTrace tailWord_740472 prefixEnd_740472 126739349065377377864879 := by
  unfold tailWord_740472
  simp only [CollatzResearch.WordTrace]
  refine ⟨13503616286701940697255835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18004821715602587596341113 13503616286701940697255835)
  ·
    refine ⟨20255424430052911045883753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13503616286701940697255835 20255424430052911045883753)
    ·
      refine ⟨15191568322539683284412815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20255424430052911045883753 15191568322539683284412815)
      ·
        refine ⟨22787352483809524926619223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15191568322539683284412815 22787352483809524926619223)
        ·
          refine ⟨34181028725714287389928835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22787352483809524926619223 34181028725714287389928835)
          ·
            refine ⟨51271543088571431084893253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34181028725714287389928835 51271543088571431084893253)
            ·
              refine ⟨9613414329107143328417485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51271543088571431084893253 9613414329107143328417485)
              ·
                refine ⟨3605030373415178748156557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9613414329107143328417485 3605030373415178748156557)
                ·
                  refine ⟨1351886390030692030558709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605030373415178748156557 1351886390030692030558709)
                  ·
                    refine ⟨126739349065377377864879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1351886390030692030558709 126739349065377377864879)
                    ·
                      rfl

theorem cell23_740472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_740472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740472 prefixEnd_740472 := by exact prefixLift 740472
  have htrace : WordTrace (prefixWord ++ tailWord_740472) baseStart_740472 baseEnd_740472 := by
    simpa [prefixWord, tailWord_740472, baseEnd_740472] using wordTrace_append hprefix tailTrace_740472
  have hstable : (prefixWord ++ tailWord_740472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740472).length < 2 ^ (prefixWord ++ tailWord_740472).sum := by decide
  have hdescent : baseEnd_740472 < baseStart_740472 := by decide
  rcases family_descends (prefixWord ++ tailWord_740472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740479 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 8, 3, 2]
def baseStart_740479 : Nat := 118140960795 + 740479 * 2 ^ 59
def prefixEnd_740479 : Nat := 4983230072969 + 3 ^ 40 * 740479 * 2
def baseEnd_740479 : Nat := 380221641560713606207105

theorem tailTrace_740479 : CollatzResearch.WordTrace tailWord_740479 prefixEnd_740479 380221641560713606207105 := by
  unfold tailWord_740479
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007487884378521590016491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18004991922919014393344327 27007487884378521590016491)
  ·
    refine ⟨40511231826567782385024737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27007487884378521590016491 40511231826567782385024737)
    ·
      refine ⟨30383423869925836788768553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40511231826567782385024737 30383423869925836788768553)
      ·
        refine ⟨22787567902444377591576415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30383423869925836788768553 22787567902444377591576415)
        ·
          refine ⟨34181351853666566387364623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22787567902444377591576415 34181351853666566387364623)
          ·
            refine ⟨51272027780499849581046935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34181351853666566387364623 51272027780499849581046935)
            ·
              refine ⟨76908041670749774371570403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51272027780499849581046935 76908041670749774371570403)
              ·
                refine ⟨115362062506124661557355605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76908041670749774371570403 115362062506124661557355605)
                ·
                  refine ⟨1351899169993648377625261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 115362062506124661557355605 1351899169993648377625261)
                  ·
                    refine ⟨506962188747618141609473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351899169993648377625261 506962188747618141609473)
                    ·
                      refine ⟨380221641560713606207105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 506962188747618141609473 380221641560713606207105)
                      ·
                        rfl

theorem cell23_740479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_740479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740479 prefixEnd_740479 := by exact prefixLift 740479
  have htrace : WordTrace (prefixWord ++ tailWord_740479) baseStart_740479 baseEnd_740479 := by
    simpa [prefixWord, tailWord_740479, baseEnd_740479] using wordTrace_append hprefix tailTrace_740479
  have hstable : (prefixWord ++ tailWord_740479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740479).length < 2 ^ (prefixWord ++ tailWord_740479).sum := by decide
  have hdescent : baseEnd_740479 < baseStart_740479 := by decide
  rcases family_descends (prefixWord ++ tailWord_740479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740489 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 1, 5]
def baseStart_740489 : Nat := 118140960795 + 740489 * 2 ^ 59
def prefixEnd_740489 : Nat := 4983230072969 + 3 ^ 40 * 740489 * 2
def baseEnd_740489 : Nat := 126742258789086189027353

theorem tailTrace_740489 : CollatzResearch.WordTrace tailWord_740489 prefixEnd_740489 126742258789086189027353 := by
  unfold tailWord_740489
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007852614342293297880521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18005235076228195531920347 27007852614342293297880521)
  ·
    refine ⟨20255889460756719973410391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27007852614342293297880521 20255889460756719973410391)
    ·
      refine ⟨30383834191135079960115587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20255889460756719973410391 30383834191135079960115587)
      ·
        refine ⟨45575751286702619940173381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30383834191135079960115587 45575751286702619940173381)
        ·
          refine ⟨8545453366256741238782509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45575751286702619940173381 8545453366256741238782509)
          ·
            refine ⟨3204545012346277964543441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8545453366256741238782509 3204545012346277964543441)
            ·
              refine ⟨2403408759259708473407581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204545012346277964543441 2403408759259708473407581)
              ·
                refine ⟨901278284722390677527843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2403408759259708473407581 901278284722390677527843)
                ·
                  refine ⟨1351917427083586016291765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901278284722390677527843 1351917427083586016291765)
                  ·
                    refine ⟨126742258789086189027353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1351917427083586016291765 126742258789086189027353)
                    ·
                      rfl

theorem cell23_740489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_740489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740489 prefixEnd_740489 := by exact prefixLift 740489
  have htrace : WordTrace (prefixWord ++ tailWord_740489) baseStart_740489 baseEnd_740489 := by
    simpa [prefixWord, tailWord_740489, baseEnd_740489] using wordTrace_append hprefix tailTrace_740489
  have hstable : (prefixWord ++ tailWord_740489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740489).length < 2 ^ (prefixWord ++ tailWord_740489).sum := by decide
  have hdescent : baseEnd_740489 < baseStart_740489 := by decide
  rcases family_descends (prefixWord ++ tailWord_740489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740503 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_740503 : Nat := 118140960795 + 740503 * 2 ^ 59
def prefixEnd_740503 : Nat := 4983230072969 + 3 ^ 40 * 740503 * 2
def baseEnd_740503 : Nat := 380233965096421512306995

theorem tailTrace_740503 : CollatzResearch.WordTrace tailWord_740503 prefixEnd_740503 380233965096421512306995 := by
  unfold tailWord_740503
  simp only [CollatzResearch.WordTrace]
  refine ⟨27008363236291573688890163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18005575490861049125926775 27008363236291573688890163)
  ·
    refine ⟨40512544854437360533335245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27008363236291573688890163 40512544854437360533335245)
    ·
      refine ⟨15192204320414010200000717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40512544854437360533335245 15192204320414010200000717)
      ·
        refine ⟨5697076620155253825000269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15192204320414010200000717 5697076620155253825000269)
        ·
          refine ⟨2136403732558220184375101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5697076620155253825000269 2136403732558220184375101)
          ·
            refine ⟨801151399709332569140663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2136403732558220184375101 801151399709332569140663)
            ·
              refine ⟨1201727099563998853710995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801151399709332569140663 1201727099563998853710995)
              ·
                refine ⟨1802590649345998280566493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201727099563998853710995 1802590649345998280566493)
                ·
                  refine ⟨675971493504749355212435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1802590649345998280566493 675971493504749355212435)
                  ·
                    refine ⟨1013957240257124032818653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 675971493504749355212435 1013957240257124032818653)
                    ·
                      refine ⟨380233965096421512306995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1013957240257124032818653 380233965096421512306995)
                      ·
                        rfl

theorem cell23_740503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_740503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740503 prefixEnd_740503 := by exact prefixLift 740503
  have htrace : WordTrace (prefixWord ++ tailWord_740503) baseStart_740503 baseEnd_740503 := by
    simpa [prefixWord, tailWord_740503, baseEnd_740503] using wordTrace_append hprefix tailTrace_740503
  have hstable : (prefixWord ++ tailWord_740503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740503).length < 2 ^ (prefixWord ++ tailWord_740503).sum := by decide
  have hdescent : baseEnd_740503 < baseStart_740503 := by decide
  rcases family_descends (prefixWord ++ tailWord_740503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740509 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_740509 : Nat := 118140960795 + 740509 * 2 ^ 59
def prefixEnd_740509 : Nat := 4983230072969 + 3 ^ 40 * 740509 * 2
def baseEnd_740509 : Nat := 380237045980348488831967

theorem tailTrace_740509 : CollatzResearch.WordTrace tailWord_740509 prefixEnd_740509 380237045980348488831967 := by
  unfold tailWord_740509
  simp only [CollatzResearch.WordTrace]
  refine ⟨27008582074269836713608581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18005721382846557809072387 27008582074269836713608581)
  ·
    refine ⟨5064109138925594383801609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27008582074269836713608581 5064109138925594383801609)
    ·
      refine ⟨3798081854194195787851207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5064109138925594383801609 3798081854194195787851207)
      ·
        refine ⟨5697122781291293681776811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3798081854194195787851207 5697122781291293681776811)
        ·
          refine ⟨8545684171936940522665217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697122781291293681776811 8545684171936940522665217)
          ·
            refine ⟨6409263128952705391998913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8545684171936940522665217 6409263128952705391998913)
            ·
              refine ⟨4806947346714529043999185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6409263128952705391998913 4806947346714529043999185)
              ·
                refine ⟨3605210510035896782999389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806947346714529043999185 3605210510035896782999389)
                ·
                  refine ⟨1351953941263461293624771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3605210510035896782999389 1351953941263461293624771)
                  ·
                    refine ⟨2027930911895191940437157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1351953941263461293624771 2027930911895191940437157)
                    ·
                      refine ⟨380237045980348488831967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2027930911895191940437157 380237045980348488831967)
                      ·
                        rfl

theorem cell23_740509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_740509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740509 prefixEnd_740509 := by exact prefixLift 740509
  have htrace : WordTrace (prefixWord ++ tailWord_740509) baseStart_740509 baseEnd_740509 := by
    simpa [prefixWord, tailWord_740509, baseEnd_740509] using wordTrace_append hprefix tailTrace_740509
  have hstable : (prefixWord ++ tailWord_740509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740509).length < 2 ^ (prefixWord ++ tailWord_740509).sum := by decide
  have hdescent : baseEnd_740509 < baseStart_740509 := by decide
  rcases family_descends (prefixWord ++ tailWord_740509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740573 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_740573 : Nat := 118140960795 + 740573 * 2 ^ 59
def prefixEnd_740573 : Nat := 4983230072969 + 3 ^ 40 * 740573 * 2
def baseEnd_740573 : Nat := 380269908742236238431673

theorem tailTrace_740573 : CollatzResearch.WordTrace tailWord_740573 prefixEnd_740573 380269908742236238431673 := by
  unfold tailWord_740573
  simp only [CollatzResearch.WordTrace]
  refine ⟨27010916346037975643938373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18007277564025317095958915 27010916346037975643938373)
  ·
    refine ⟨5064546814882120433238445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27010916346037975643938373 5064546814882120433238445)
    ·
      refine ⟨1899205055580795162464417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5064546814882120433238445 1899205055580795162464417)
      ·
        refine ⟨1424403791685596371848313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1899205055580795162464417 1424403791685596371848313)
        ·
          refine ⟨1068302843764197278886235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424403791685596371848313 1068302843764197278886235)
          ·
            refine ⟨1602454265646295918329353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068302843764197278886235 1602454265646295918329353)
            ·
              refine ⟨1201840699234721938747015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602454265646295918329353 1201840699234721938747015)
              ·
                refine ⟨1802761048852082908120523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201840699234721938747015 1802761048852082908120523)
                ·
                  refine ⟨2704141573278124362180785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802761048852082908120523 2704141573278124362180785)
                  ·
                    refine ⟨2028106179958593271635589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2704141573278124362180785 2028106179958593271635589)
                    ·
                      refine ⟨380269908742236238431673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2028106179958593271635589 380269908742236238431673)
                      ·
                        rfl

theorem cell23_740573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_740573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740573 prefixEnd_740573 := by exact prefixLift 740573
  have htrace : WordTrace (prefixWord ++ tailWord_740573) baseStart_740573 baseEnd_740573 := by
    simpa [prefixWord, tailWord_740573, baseEnd_740573] using wordTrace_append hprefix tailTrace_740573
  have hstable : (prefixWord ++ tailWord_740573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740573).length < 2 ^ (prefixWord ++ tailWord_740573).sum := by decide
  have hdescent : baseEnd_740573 < baseStart_740573 := by decide
  rcases family_descends (prefixWord ++ tailWord_740573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740576 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 3]
def baseStart_740576 : Nat := 118140960795 + 740576 * 2 ^ 59
def prefixEnd_740576 : Nat := 4983230072969 + 3 ^ 40 * 740576 * 2
def baseEnd_740576 : Nat := 380271449184199726694159

theorem tailTrace_740576 : CollatzResearch.WordTrace tailWord_740576 prefixEnd_740576 380271449184199726694159 := by
  unfold tailWord_740576
  simp only [CollatzResearch.WordTrace]
  refine ⟨13505512882513553578148791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18007350510018071437531721 13505512882513553578148791)
  ·
    refine ⟨20258269323770330367223187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13505512882513553578148791 20258269323770330367223187)
    ·
      refine ⟨30387403985655495550834781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20258269323770330367223187 30387403985655495550834781)
      ·
        refine ⟨11395276494620810831563043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30387403985655495550834781 11395276494620810831563043)
        ·
          refine ⟨17092914741931216247344565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11395276494620810831563043 17092914741931216247344565)
          ·
            refine ⟨1602460757056051523188553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17092914741931216247344565 1602460757056051523188553)
            ·
              refine ⟨1201845567792038642391415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602460757056051523188553 1201845567792038642391415)
              ·
                refine ⟨1802768351688057963587123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201845567792038642391415 1802768351688057963587123)
                ·
                  refine ⟨2704152527532086945380685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802768351688057963587123 2704152527532086945380685)
                  ·
                    refine ⟨1014057197824532604517757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2704152527532086945380685 1014057197824532604517757)
                    ·
                      refine ⟨380271449184199726694159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014057197824532604517757 380271449184199726694159)
                      ·
                        rfl

theorem cell23_740576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_740576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740576 prefixEnd_740576 := by exact prefixLift 740576
  have htrace : WordTrace (prefixWord ++ tailWord_740576) baseStart_740576 baseEnd_740576 := by
    simpa [prefixWord, tailWord_740576, baseEnd_740576] using wordTrace_append hprefix tailTrace_740576
  have hstable : (prefixWord ++ tailWord_740576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740576).length < 2 ^ (prefixWord ++ tailWord_740576).sum := by decide
  have hdescent : baseEnd_740576 < baseStart_740576 := by decide
  rcases family_descends (prefixWord ++ tailWord_740576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740609 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 2, 6]
def baseStart_740609 : Nat := 118140960795 + 740609 * 2 ^ 59
def prefixEnd_740609 : Nat := 4983230072969 + 3 ^ 40 * 740609 * 2
def baseEnd_740609 : Nat := 126762798015266032527169

theorem tailTrace_740609 : CollatzResearch.WordTrace tailWord_740609 prefixEnd_740609 126762798015266032527169 := by
  unfold tailWord_740609
  simp only [CollatzResearch.WordTrace]
  refine ⟨27012229373907553792248881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18008152915938369194832587 27012229373907553792248881)
  ·
    refine ⟨20259172030430665344186661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27012229373907553792248881 20259172030430665344186661)
    ·
      refine ⟨3798594755705749752034999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20259172030430665344186661 3798594755705749752034999)
      ·
        refine ⟨5697892133558624628052499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3798594755705749752034999 5697892133558624628052499)
        ·
          refine ⟨8546838200337936942078749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5697892133558624628052499 8546838200337936942078749)
          ·
            refine ⟨3205064325126726353279531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8546838200337936942078749 3205064325126726353279531)
            ·
              refine ⟨4807596487690089529919297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205064325126726353279531 4807596487690089529919297)
              ·
                refine ⟨3605697365767567147439473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807596487690089529919297 3605697365767567147439473)
                ·
                  refine ⟨2704273024325675360579605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3605697365767567147439473 2704273024325675360579605)
                  ·
                    refine ⟨126762798015266032527169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2704273024325675360579605 126762798015266032527169)
                    ·
                      rfl

theorem cell23_740609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_740609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740609 prefixEnd_740609 := by exact prefixLift 740609
  have htrace : WordTrace (prefixWord ++ tailWord_740609) baseStart_740609 baseEnd_740609 := by
    simpa [prefixWord, tailWord_740609, baseEnd_740609] using wordTrace_append hprefix tailTrace_740609
  have hstable : (prefixWord ++ tailWord_740609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740609).length < 2 ^ (prefixWord ++ tailWord_740609).sum := by decide
  have hdescent : baseEnd_740609 < baseStart_740609 := by decide
  rcases family_descends (prefixWord ++ tailWord_740609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740610 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_740610 : Nat := 118140960795 + 740610 * 2 ^ 59
def prefixEnd_740610 : Nat := 4983230072969 + 3 ^ 40 * 740610 * 2
def baseEnd_740610 : Nat := 380288907526452593669003

theorem tailTrace_740610 : CollatzResearch.WordTrace tailWord_740610 prefixEnd_740610 380288907526452593669003 := by
  unfold tailWord_740610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753066461725982740758821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18008177231269287308690189 6753066461725982740758821)
  ·
    refine ⟨1266199961573621763892279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6753066461725982740758821 1266199961573621763892279)
    ·
      refine ⟨1899299942360432645838419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266199961573621763892279 1899299942360432645838419)
      ·
        refine ⟨2848949913540648968757629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899299942360432645838419 2848949913540648968757629)
        ·
          refine ⟨1068356217577743363284111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2848949913540648968757629 1068356217577743363284111)
          ·
            refine ⟨1602534326366615044926167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068356217577743363284111 1602534326366615044926167)
            ·
              refine ⟨2403801489549922567389251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602534326366615044926167 2403801489549922567389251)
              ·
                refine ⟨3605702234324883851083877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403801489549922567389251 3605702234324883851083877)
                ·
                  refine ⟨676069168935915722078227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3605702234324883851083877 676069168935915722078227)
                  ·
                    refine ⟨1014103753403873583117341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 676069168935915722078227 1014103753403873583117341)
                    ·
                      refine ⟨380288907526452593669003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014103753403873583117341 380288907526452593669003)
                      ·
                        rfl

theorem cell23_740610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_740610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740610 prefixEnd_740610 := by exact prefixLift 740610
  have htrace : WordTrace (prefixWord ++ tailWord_740610) baseStart_740610 baseEnd_740610 := by
    simpa [prefixWord, tailWord_740610, baseEnd_740610] using wordTrace_append hprefix tailTrace_740610
  have hstable : (prefixWord ++ tailWord_740610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740610).length < 2 ^ (prefixWord ++ tailWord_740610).sum := by decide
  have hdescent : baseEnd_740610 < baseStart_740610 := by decide
  rcases family_descends (prefixWord ++ tailWord_740610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740650 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_740650 : Nat := 118140960795 + 740650 * 2 ^ 59
def prefixEnd_740650 : Nat := 4983230072969 + 3 ^ 40 * 740650 * 2
def baseEnd_740650 : Nat := 380309446752632437168819

theorem tailTrace_740650 : CollatzResearch.WordTrace tailWord_740650 prefixEnd_740650 380309446752632437168819 := by
  unfold tailWord_740650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6753431191689754448622851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18009149844506011862994269 6753431191689754448622851)
  ·
    refine ⟨10130146787534631672934277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6753431191689754448622851 10130146787534631672934277)
    ·
      refine ⟨1899402522662743438675177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10130146787534631672934277 1899402522662743438675177)
      ·
        refine ⟨1424551891997057579006383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1899402522662743438675177 1424551891997057579006383)
        ·
          refine ⟨2136827837995586368509575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424551891997057579006383 2136827837995586368509575)
          ·
            refine ⟨3205241756993379552764363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136827837995586368509575 3205241756993379552764363)
            ·
              refine ⟨4807862635490069329146545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205241756993379552764363 4807862635490069329146545)
              ·
                refine ⟨3605896976617551996859909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807862635490069329146545 3605896976617551996859909)
                ·
                  refine ⟨676105683115790999411233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3605896976617551996859909 676105683115790999411233)
                  ·
                    refine ⟨507079262336843249558425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 676105683115790999411233 507079262336843249558425)
                    ·
                      refine ⟨380309446752632437168819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507079262336843249558425 380309446752632437168819)
                      ·
                        rfl

theorem cell23_740650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_740650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740650 prefixEnd_740650 := by exact prefixLift 740650
  have htrace : WordTrace (prefixWord ++ tailWord_740650) baseStart_740650 baseEnd_740650 := by
    simpa [prefixWord, tailWord_740650, baseEnd_740650] using wordTrace_append hprefix tailTrace_740650
  have hstable : (prefixWord ++ tailWord_740650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740650).length < 2 ^ (prefixWord ++ tailWord_740650).sum := by decide
  have hdescent : baseEnd_740650 < baseStart_740650 := by decide
  rcases family_descends (prefixWord ++ tailWord_740650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740653 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_740653 : Nat := 118140960795 + 740653 * 2 ^ 59
def prefixEnd_740653 : Nat := 4983230072969 + 3 ^ 40 * 740653 * 2
def baseEnd_740653 : Nat := 380310987194595925431305

theorem tailTrace_740653 : CollatzResearch.WordTrace tailWord_740653 prefixEnd_740653 380310987194595925431305 := by
  unfold tailWord_740653
  simp only [CollatzResearch.WordTrace]
  refine ⟨27013834185748149306850613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18009222790498766204567075 27013834185748149306850613)
  ·
    refine ⟨2532546954913888997517245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27013834185748149306850613 2532546954913888997517245)
    ·
      refine ⟨949705108092708374068967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2532546954913888997517245 949705108092708374068967)
      ·
        refine ⟨1424557662139062561103451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949705108092708374068967 1424557662139062561103451)
        ·
          refine ⟨2136836493208593841655177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424557662139062561103451 2136836493208593841655177)
          ·
            refine ⟨1602627369906445381241383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2136836493208593841655177 1602627369906445381241383)
            ·
              refine ⟨2403941054859668071862075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602627369906445381241383 2403941054859668071862075)
              ·
                refine ⟨3605911582289502107793113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403941054859668071862075 3605911582289502107793113)
                ·
                  refine ⟨2704433686717126580844835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3605911582289502107793113 2704433686717126580844835)
                  ·
                    refine ⟨4056650530075689871267253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2704433686717126580844835 4056650530075689871267253)
                    ·
                      refine ⟨380310987194595925431305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4056650530075689871267253 380310987194595925431305)
                      ·
                        rfl

theorem cell23_740653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_740653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740653 prefixEnd_740653 := by exact prefixLift 740653
  have htrace : WordTrace (prefixWord ++ tailWord_740653) baseStart_740653 baseEnd_740653 := by
    simpa [prefixWord, tailWord_740653, baseEnd_740653] using wordTrace_append hprefix tailTrace_740653
  have hstable : (prefixWord ++ tailWord_740653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740653).length < 2 ^ (prefixWord ++ tailWord_740653).sum := by decide
  have hdescent : baseEnd_740653 < baseStart_740653 := by decide
  rcases family_descends (prefixWord ++ tailWord_740653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740673 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 7]
def baseStart_740673 : Nat := 118140960795 + 740673 * 2 ^ 59
def prefixEnd_740673 : Nat := 4983230072969 + 3 ^ 40 * 740673 * 2
def baseEnd_740673 : Nat := 42257917423076205242357

theorem tailTrace_740673 : CollatzResearch.WordTrace tailWord_740673 prefixEnd_740673 42257917423076205242357 := by
  unfold tailWord_740673
  simp only [CollatzResearch.WordTrace]
  refine ⟨27014563645675692722578673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18009709097117128481719115 27014563645675692722578673)
  ·
    refine ⟨20260922734256769541934005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27014563645675692722578673 20260922734256769541934005)
    ·
      refine ⟨1899461506336572144556313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20260922734256769541934005 1899461506336572144556313)
      ·
        refine ⟨1424596129752429108417235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1899461506336572144556313 1424596129752429108417235)
        ·
          refine ⟨2136894194628643662625853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424596129752429108417235 2136894194628643662625853)
          ·
            refine ⟨801335322985741373484695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2136894194628643662625853 801335322985741373484695)
            ·
              refine ⟨1202002984478612060227043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801335322985741373484695 1202002984478612060227043)
              ·
                refine ⟨1803004476717918090340565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202002984478612060227043 1803004476717918090340565)
                ·
                  refine ⟨42257917423076205242357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1803004476717918090340565 42257917423076205242357)
                  ·
                    rfl

theorem cell23_740673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 7].length) (baseStart_740673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740673 prefixEnd_740673 := by exact prefixLift 740673
  have htrace : WordTrace (prefixWord ++ tailWord_740673) baseStart_740673 baseEnd_740673 := by
    simpa [prefixWord, tailWord_740673, baseEnd_740673] using wordTrace_append hprefix tailTrace_740673
  have hstable : (prefixWord ++ tailWord_740673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740673).length < 2 ^ (prefixWord ++ tailWord_740673).sum := by decide
  have hdescent : baseEnd_740673 < baseStart_740673 := by decide
  rcases family_descends (prefixWord ++ tailWord_740673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740678 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_740678 : Nat := 118140960795 + 740678 * 2 ^ 59
def prefixEnd_740678 : Nat := 4983230072969 + 3 ^ 40 * 740678 * 2
def baseEnd_740678 : Nat := 380323824210958327618691

theorem tailTrace_740678 : CollatzResearch.WordTrace tailWord_740678 prefixEnd_740678 380323824210958327618691 := by
  unfold tailWord_740678
  simp only [CollatzResearch.WordTrace]
  refine ⟨844210812833049330515959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18009830673771719051007125 844210812833049330515959)
  ·
    refine ⟨1266316219249573995773939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 844210812833049330515959 1266316219249573995773939)
    ·
      refine ⟨1899474328874360993660909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266316219249573995773939 1899474328874360993660909)
      ·
        refine ⟨712302873327885372622841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1899474328874360993660909 712302873327885372622841)
        ·
          refine ⟨534227154995914029467131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 712302873327885372622841 534227154995914029467131)
          ·
            refine ⟨801340732493871044200697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534227154995914029467131 801340732493871044200697)
            ·
              refine ⟨601005549370403283150523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801340732493871044200697 601005549370403283150523)
              ·
                refine ⟨901508324055604924725785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601005549370403283150523 901508324055604924725785)
                ·
                  refine ⟨676131243041703693544339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 901508324055604924725785 676131243041703693544339)
                  ·
                    refine ⟨1014196864562555540316509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 676131243041703693544339 1014196864562555540316509)
                    ·
                      refine ⟨380323824210958327618691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014196864562555540316509 380323824210958327618691)
                      ·
                        rfl

theorem cell23_740678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_740678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740678 prefixEnd_740678 := by exact prefixLift 740678
  have htrace : WordTrace (prefixWord ++ tailWord_740678) baseStart_740678 baseEnd_740678 := by
    simpa [prefixWord, tailWord_740678, baseEnd_740678] using wordTrace_append hprefix tailTrace_740678
  have hstable : (prefixWord ++ tailWord_740678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740678).length < 2 ^ (prefixWord ++ tailWord_740678).sum := by decide
  have hdescent : baseEnd_740678 < baseStart_740678 := by decide
  rcases family_descends (prefixWord ++ tailWord_740678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740679 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_740679 : Nat := 118140960795 + 740679 * 2 ^ 59
def prefixEnd_740679 : Nat := 4983230072969 + 3 ^ 40 * 740679 * 2
def baseEnd_740679 : Nat := 380324337691612823706185

theorem tailTrace_740679 : CollatzResearch.WordTrace tailWord_740679 prefixEnd_740679 380324337691612823706185 := by
  unfold tailWord_740679
  simp only [CollatzResearch.WordTrace]
  refine ⟨27014782483653955747297091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18009854989102637164864727 27014782483653955747297091)
  ·
    refine ⟨40522173725480933620945637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27014782483653955747297091 40522173725480933620945637)
    ·
      refine ⟨7597907573527675053927307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40522173725480933620945637 7597907573527675053927307)
      ·
        refine ⟨11396861360291512580890961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7597907573527675053927307 11396861360291512580890961)
        ·
          refine ⟨8547646020218634435668221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11396861360291512580890961 8547646020218634435668221)
          ·
            refine ⟨3205367257581987913375583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8547646020218634435668221 3205367257581987913375583)
            ·
              refine ⟨4808050886372981870063375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205367257581987913375583 4808050886372981870063375)
              ·
                refine ⟨7212076329559472805095063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808050886372981870063375 7212076329559472805095063)
                ·
                  refine ⟨10818114494339209207642595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212076329559472805095063 10818114494339209207642595)
                  ·
                    refine ⟨16227171741508813811463893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10818114494339209207642595 16227171741508813811463893)
                    ·
                      refine ⟨380324337691612823706185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16227171741508813811463893 380324337691612823706185)
                      ·
                        rfl

theorem cell23_740679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_740679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740679 prefixEnd_740679 := by exact prefixLift 740679
  have htrace : WordTrace (prefixWord ++ tailWord_740679) baseStart_740679 baseEnd_740679 := by
    simpa [prefixWord, tailWord_740679, baseEnd_740679] using wordTrace_append hprefix tailTrace_740679
  have hstable : (prefixWord ++ tailWord_740679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740679).length < 2 ^ (prefixWord ++ tailWord_740679).sum := by decide
  have hdescent : baseEnd_740679 < baseStart_740679 := by decide
  rcases family_descends (prefixWord ++ tailWord_740679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740719 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 6]
def baseStart_740719 : Nat := 118140960795 + 740719 * 2 ^ 59
def prefixEnd_740719 : Nat := 4983230072969 + 3 ^ 40 * 740719 * 2
def baseEnd_740719 : Nat := 380344876917792667206001

theorem tailTrace_740719 : CollatzResearch.WordTrace tailWord_740719 prefixEnd_740719 380344876917792667206001 := by
  unfold tailWord_740719
  simp only [CollatzResearch.WordTrace]
  refine ⟨27016241403509042578753211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18010827602339361719168807 27016241403509042578753211)
  ·
    refine ⟨40524362105263563868129817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27016241403509042578753211 40524362105263563868129817)
    ·
      refine ⟨30393271578947672901097363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40524362105263563868129817 30393271578947672901097363)
      ·
        refine ⟨45589907368421509351646045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30393271578947672901097363 45589907368421509351646045)
        ·
          refine ⟨17096215263158066006867267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45589907368421509351646045 17096215263158066006867267)
          ·
            refine ⟨25644322894737099010300901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17096215263158066006867267 25644322894737099010300901)
            ·
              refine ⟨4808310542763206064431419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25644322894737099010300901 4808310542763206064431419)
              ·
                refine ⟨7212465814144809096647129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808310542763206064431419 7212465814144809096647129)
                ·
                  refine ⟨5409349360608606822485347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7212465814144809096647129 5409349360608606822485347)
                  ·
                    refine ⟨8114024040912910233728021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5409349360608606822485347 8114024040912910233728021)
                    ·
                      refine ⟨380344876917792667206001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8114024040912910233728021 380344876917792667206001)
                      ·
                        rfl

theorem cell23_740719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_740719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740719 prefixEnd_740719 := by exact prefixLift 740719
  have htrace : WordTrace (prefixWord ++ tailWord_740719) baseStart_740719 baseEnd_740719 := by
    simpa [prefixWord, tailWord_740719, baseEnd_740719] using wordTrace_append hprefix tailTrace_740719
  have hstable : (prefixWord ++ tailWord_740719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740719).length < 2 ^ (prefixWord ++ tailWord_740719).sum := by decide
  have hdescent : baseEnd_740719 < baseStart_740719 := by decide
  rcases family_descends (prefixWord ++ tailWord_740719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740729 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 8]
def baseStart_740729 : Nat := 118140960795 + 740729 * 2 ^ 59
def prefixEnd_740729 : Nat := 4983230072969 + 3 ^ 40 * 740729 * 2
def baseEnd_740729 : Nat := 42261112413815292008995

theorem tailTrace_740729 : CollatzResearch.WordTrace tailWord_740729 prefixEnd_740729 42261112413815292008995 := by
  unfold tailWord_740729
  simp only [CollatzResearch.WordTrace]
  refine ⟨27016606133472814286617241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18011070755648542857744827 27016606133472814286617241)
  ·
    refine ⟨20262454600104610714962931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27016606133472814286617241 20262454600104610714962931)
    ·
      refine ⟨30393681900156916072444397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20262454600104610714962931 30393681900156916072444397)
      ·
        refine ⟨11397630712558843527166649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30393681900156916072444397 11397630712558843527166649)
        ·
          refine ⟨8548223034419132645374987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11397630712558843527166649 8548223034419132645374987)
          ·
            refine ⟨12822334551628698968062481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8548223034419132645374987 12822334551628698968062481)
            ·
              refine ⟨9616750913721524226046861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12822334551628698968062481 9616750913721524226046861)
              ·
                refine ⟨3606281592645571584767573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9616750913721524226046861 3606281592645571584767573)
                ·
                  refine ⟨42261112413815292008995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3606281592645571584767573 42261112413815292008995)
                  ·
                    rfl

theorem cell23_740729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 8].length) (baseStart_740729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740729 prefixEnd_740729 := by exact prefixLift 740729
  have htrace : WordTrace (prefixWord ++ tailWord_740729) baseStart_740729 baseEnd_740729 := by
    simpa [prefixWord, tailWord_740729, baseEnd_740729] using wordTrace_append hprefix tailTrace_740729
  have hstable : (prefixWord ++ tailWord_740729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740729).length < 2 ^ (prefixWord ++ tailWord_740729).sum := by decide
  have hdescent : baseEnd_740729 < baseStart_740729 := by decide
  rcases family_descends (prefixWord ++ tailWord_740729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740750 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_740750 : Nat := 118140960795 + 740750 * 2 ^ 59
def prefixEnd_740750 : Nat := 4983230072969 + 3 ^ 40 * 740750 * 2
def baseEnd_740750 : Nat := 126786931606027348639453

theorem tailTrace_740750 : CollatzResearch.WordTrace tailWord_740750 prefixEnd_740750 126786931606027348639453 := by
  unfold tailWord_740750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377171508299591859141463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18011581377597823248754469 3377171508299591859141463)
  ·
    refine ⟨5065757262449387788712195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3377171508299591859141463 5065757262449387788712195)
    ·
      refine ⟨7598635893674081683068293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5065757262449387788712195 7598635893674081683068293)
      ·
        refine ⟨1424744230063890315575305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7598635893674081683068293 1424744230063890315575305)
        ·
          refine ⟨1068558172547917736681479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424744230063890315575305 1068558172547917736681479)
          ·
            refine ⟨1602837258821876605022219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068558172547917736681479 1602837258821876605022219)
            ·
              refine ⟨2404255888232814907533329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602837258821876605022219 2404255888232814907533329)
              ·
                refine ⟨1803191916174611180649997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404255888232814907533329 1803191916174611180649997)
                ·
                  refine ⟨676196968565479192743749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1803191916174611180649997 676196968565479192743749)
                  ·
                    refine ⟨126786931606027348639453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 676196968565479192743749 126786931606027348639453)
                    ·
                      rfl

theorem cell23_740750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_740750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740750 prefixEnd_740750 := by exact prefixLift 740750
  have htrace : WordTrace (prefixWord ++ tailWord_740750) baseStart_740750 baseEnd_740750 := by
    simpa [prefixWord, tailWord_740750, baseEnd_740750] using wordTrace_append hprefix tailTrace_740750
  have hstable : (prefixWord ++ tailWord_740750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740750).length < 2 ^ (prefixWord ++ tailWord_740750).sum := by decide
  have hdescent : baseEnd_740750 < baseStart_740750 := by decide
  rcases family_descends (prefixWord ++ tailWord_740750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740783 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 2, 3, 2]
def baseStart_740783 : Nat := 118140960795 + 740783 * 2 ^ 59
def prefixEnd_740783 : Nat := 4983230072969 + 3 ^ 40 * 740783 * 2
def baseEnd_740783 : Nat := 380377739679680416805707

theorem tailTrace_740783 : CollatzResearch.WordTrace tailWord_740783 prefixEnd_740783 380377739679680416805707 := by
  unfold tailWord_740783
  simp only [CollatzResearch.WordTrace]
  refine ⟨27018575675277181509083003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18012383783518121006055335 27018575675277181509083003)
  ·
    refine ⟨40527863512915772263624505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27018575675277181509083003 40527863512915772263624505)
    ·
      refine ⟨30395897634686829197718379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40527863512915772263624505 30395897634686829197718379)
      ·
        refine ⟨45593846452030243796577569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30395897634686829197718379 45593846452030243796577569)
        ·
          refine ⟨34195384839022682847433177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45593846452030243796577569 34195384839022682847433177)
          ·
            refine ⟨25646538629267012135574883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34195384839022682847433177 25646538629267012135574883)
            ·
              refine ⟨38469807943900518203362325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25646538629267012135574883 38469807943900518203362325)
              ·
                refine ⟨1803272247370336790782609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38469807943900518203362325 1803272247370336790782609)
                ·
                  refine ⟨1352454185527752593086957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803272247370336790782609 1352454185527752593086957)
                  ·
                    refine ⟨507170319572907222407609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352454185527752593086957 507170319572907222407609)
                    ·
                      refine ⟨380377739679680416805707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507170319572907222407609 380377739679680416805707)
                      ·
                        rfl

theorem cell23_740783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 3, 2].length) (baseStart_740783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740783 prefixEnd_740783 := by exact prefixLift 740783
  have htrace : WordTrace (prefixWord ++ tailWord_740783) baseStart_740783 baseEnd_740783 := by
    simpa [prefixWord, tailWord_740783, baseEnd_740783] using wordTrace_append hprefix tailTrace_740783
  have hstable : (prefixWord ++ tailWord_740783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740783).length < 2 ^ (prefixWord ++ tailWord_740783).sum := by decide
  have hdescent : baseEnd_740783 < baseStart_740783 := by decide
  rcases family_descends (prefixWord ++ tailWord_740783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740833 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_740833 : Nat := 118140960795 + 740833 * 2 ^ 59
def prefixEnd_740833 : Nat := 4983230072969 + 3 ^ 40 * 740833 * 2
def baseEnd_740833 : Nat := 380403413712405221180477

theorem tailTrace_740833 : CollatzResearch.WordTrace tailWord_740833 prefixEnd_740833 380403413712405221180477 := by
  unfold tailWord_740833
  simp only [CollatzResearch.WordTrace]
  refine ⟨27020399325096040048403153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18013599550064026698935435 27020399325096040048403153)
  ·
    refine ⟨20265299493822030036302365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27020399325096040048403153 20265299493822030036302365)
    ·
      refine ⟨7599487310183261263613387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20265299493822030036302365 7599487310183261263613387)
      ·
        refine ⟨11399230965274891895420081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7599487310183261263613387 11399230965274891895420081)
        ·
          refine ⟨8549423223956168921565061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11399230965274891895420081 8549423223956168921565061)
          ·
            refine ⟨1603016854491781672793449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8549423223956168921565061 1603016854491781672793449)
            ·
              refine ⟨1202262640868836254595087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603016854491781672793449 1202262640868836254595087)
              ·
                refine ⟨1803393961303254381892631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202262640868836254595087 1803393961303254381892631)
                ·
                  refine ⟨2705090941954881572838947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803393961303254381892631 2705090941954881572838947)
                  ·
                    refine ⟨4057636412932322359258421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705090941954881572838947 4057636412932322359258421)
                    ·
                      refine ⟨380403413712405221180477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4057636412932322359258421 380403413712405221180477)
                      ·
                        rfl

theorem cell23_740833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_740833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740833 prefixEnd_740833 := by exact prefixLift 740833
  have htrace : WordTrace (prefixWord ++ tailWord_740833) baseStart_740833 baseEnd_740833 := by
    simpa [prefixWord, tailWord_740833, baseEnd_740833] using wordTrace_append hprefix tailTrace_740833
  have hstable : (prefixWord ++ tailWord_740833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740833).length < 2 ^ (prefixWord ++ tailWord_740833).sum := by decide
  have hdescent : baseEnd_740833 < baseStart_740833 := by decide
  rcases family_descends (prefixWord ++ tailWord_740833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740847 : List Nat := [1, 1, 2, 1, 4, 1, 2, 6, 1, 2, 2]
def baseStart_740847 : Nat := 118140960795 + 740847 * 2 ^ 59
def prefixEnd_740847 : Nat := 4983230072969 + 3 ^ 40 * 740847 * 2
def baseEnd_740847 : Nat := 380410602441568166405413

theorem tailTrace_740847 : CollatzResearch.WordTrace tailWord_740847 prefixEnd_740847 380410602441568166405413 := by
  unfold tailWord_740847
  simp only [CollatzResearch.WordTrace]
  refine ⟨27020909947045320439412795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18013939964696880292941863 27020909947045320439412795)
  ·
    refine ⟨40531364920567980659119193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27020909947045320439412795 40531364920567980659119193)
    ·
      refine ⟨30398523690425985494339395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40531364920567980659119193 30398523690425985494339395)
      ·
        refine ⟨45597785535638978241509093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30398523690425985494339395 45597785535638978241509093)
        ·
          refine ⟨8549584787932308420282955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45597785535638978241509093 8549584787932308420282955)
          ·
            refine ⟨12824377181898462630424433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8549584787932308420282955 12824377181898462630424433)
            ·
              refine ⟨9618282886423846972818325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12824377181898462630424433 9618282886423846972818325)
              ·
                refine ⟨450857010301117826850859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9618282886423846972818325 450857010301117826850859)
                ·
                  refine ⟨676285515451676740276289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450857010301117826850859 676285515451676740276289)
                  ·
                    refine ⟨507214136588757555207217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 676285515451676740276289 507214136588757555207217)
                    ·
                      refine ⟨380410602441568166405413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507214136588757555207217 380410602441568166405413)
                      ·
                        rfl

theorem cell23_740847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 6, 1, 2, 2].length) (baseStart_740847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740847 prefixEnd_740847 := by exact prefixLift 740847
  have htrace : WordTrace (prefixWord ++ tailWord_740847) baseStart_740847 baseEnd_740847 := by
    simpa [prefixWord, tailWord_740847, baseEnd_740847] using wordTrace_append hprefix tailTrace_740847
  have hstable : (prefixWord ++ tailWord_740847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740847).length < 2 ^ (prefixWord ++ tailWord_740847).sum := by decide
  have hdescent : baseEnd_740847 < baseStart_740847 := by decide
  rcases family_descends (prefixWord ++ tailWord_740847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740853 : List Nat := [1, 3, 5, 1, 1, 1, 1, 10]
def baseStart_740853 : Nat := 118140960795 + 740853 * 2 ^ 59
def prefixEnd_740853 : Nat := 4983230072969 + 3 ^ 40 * 740853 * 2
def baseEnd_740853 : Nat := 14089395678722042330755

theorem tailTrace_740853 : CollatzResearch.WordTrace tailWord_740853 prefixEnd_740853 14089395678722042330755 := by
  unfold tailWord_740853
  simp only [CollatzResearch.WordTrace]
  refine ⟨27021128785023583464131213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18014085856682388976087475 27021128785023583464131213)
  ·
    refine ⟨10132923294383843799049205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27021128785023583464131213 10132923294383843799049205)
    ·
      refine ⟨949961558848485356160863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10132923294383843799049205 949961558848485356160863)
      ·
        refine ⟨1424942338272728034241295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949961558848485356160863 1424942338272728034241295)
        ·
          refine ⟨2137413507409092051361943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424942338272728034241295 2137413507409092051361943)
          ·
            refine ⟨3206120261113638077042915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137413507409092051361943 3206120261113638077042915)
            ·
              refine ⟨4809180391670457115564373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206120261113638077042915 4809180391670457115564373)
              ·
                refine ⟨14089395678722042330755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4809180391670457115564373 14089395678722042330755)
                ·
                  rfl

theorem cell23_740853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 10].length) (baseStart_740853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740853 prefixEnd_740853 := by exact prefixLift 740853
  have htrace : WordTrace (prefixWord ++ tailWord_740853) baseStart_740853 baseEnd_740853 := by
    simpa [prefixWord, tailWord_740853, baseEnd_740853] using wordTrace_append hprefix tailTrace_740853
  have hstable : (prefixWord ++ tailWord_740853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740853).length < 2 ^ (prefixWord ++ tailWord_740853).sum := by decide
  have hdescent : baseEnd_740853 < baseStart_740853 := by decide
  rcases family_descends (prefixWord ++ tailWord_740853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740863 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 3]
def baseStart_740863 : Nat := 118140960795 + 740863 * 2 ^ 59
def prefixEnd_740863 : Nat := 4983230072969 + 3 ^ 40 * 740863 * 2
def baseEnd_740863 : Nat := 380418818132040103805339

theorem tailTrace_740863 : CollatzResearch.WordTrace tailWord_740863 prefixEnd_740863 380418818132040103805339 := by
  unfold tailWord_740863
  simp only [CollatzResearch.WordTrace]
  refine ⟨27021493514987355171995243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18014329009991570114663495 27021493514987355171995243)
  ·
    refine ⟨40532240272481032757992865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27021493514987355171995243 40532240272481032757992865)
    ·
      refine ⟨30399180204360774568494649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40532240272481032757992865 30399180204360774568494649)
      ·
        refine ⟨22799385153270580926370987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30399180204360774568494649 22799385153270580926370987)
        ·
          refine ⟨34199077729905871389556481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22799385153270580926370987 34199077729905871389556481)
          ·
            refine ⟨25649308297429403542167361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34199077729905871389556481 25649308297429403542167361)
            ·
              refine ⟨19236981223072052656625521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25649308297429403542167361 19236981223072052656625521)
              ·
                refine ⟨14427735917304039492469141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19236981223072052656625521 14427735917304039492469141)
                ·
                  refine ⟨676300121123626851209491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14427735917304039492469141 676300121123626851209491)
                  ·
                    refine ⟨1014450181685440276814237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 676300121123626851209491 1014450181685440276814237)
                    ·
                      refine ⟨380418818132040103805339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014450181685440276814237 380418818132040103805339)
                      ·
                        rfl

theorem cell23_740863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_740863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740863 prefixEnd_740863 := by exact prefixLift 740863
  have htrace : WordTrace (prefixWord ++ tailWord_740863) baseStart_740863 baseEnd_740863 := by
    simpa [prefixWord, tailWord_740863, baseEnd_740863] using wordTrace_append hprefix tailTrace_740863
  have hstable : (prefixWord ++ tailWord_740863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740863).length < 2 ^ (prefixWord ++ tailWord_740863).sum := by decide
  have hdescent : baseEnd_740863 < baseStart_740863 := by decide
  rcases family_descends (prefixWord ++ tailWord_740863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740884 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_740884 : Nat := 118140960795 + 740884 * 2 ^ 59
def prefixEnd_740884 : Nat := 4983230072969 + 3 ^ 40 * 740884 * 2
def baseEnd_740884 : Nat := 380429601225784521642743

theorem tailTrace_740884 : CollatzResearch.WordTrace tailWord_740884 prefixEnd_740884 380429601225784521642743 := by
  unfold tailWord_740884
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511129723955637879254853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18014839631940850505673137 13511129723955637879254853)
  ·
    refine ⟨2533336823241682102360285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13511129723955637879254853 2533336823241682102360285)
    ·
      refine ⟨950001308715630788385107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2533336823241682102360285 950001308715630788385107)
      ·
        refine ⟨1425001963073446182577661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950001308715630788385107 1425001963073446182577661)
        ·
          refine ⟨534375736152542318466623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1425001963073446182577661 534375736152542318466623)
          ·
            refine ⟨801563604228813477699935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534375736152542318466623 801563604228813477699935)
            ·
              refine ⟨1202345406343220216549903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801563604228813477699935 1202345406343220216549903)
              ·
                refine ⟨1803518109514830324824855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202345406343220216549903 1803518109514830324824855)
                ·
                  refine ⟨2705277164272245487237283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803518109514830324824855 2705277164272245487237283)
                  ·
                    refine ⟨4057915746408368230855925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705277164272245487237283 4057915746408368230855925)
                    ·
                      refine ⟨380429601225784521642743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4057915746408368230855925 380429601225784521642743)
                      ·
                        rfl

theorem cell23_740884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_740884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740884 prefixEnd_740884 := by exact prefixLift 740884
  have htrace : WordTrace (prefixWord ++ tailWord_740884) baseStart_740884 baseEnd_740884 := by
    simpa [prefixWord, tailWord_740884, baseEnd_740884] using wordTrace_append hprefix tailTrace_740884
  have hstable : (prefixWord ++ tailWord_740884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740884).length < 2 ^ (prefixWord ++ tailWord_740884).sum := by decide
  have hdescent : baseEnd_740884 < baseStart_740884 := by decide
  rcases family_descends (prefixWord ++ tailWord_740884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740897 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_740897 : Nat := 118140960795 + 740897 * 2 ^ 59
def prefixEnd_740897 : Nat := 4983230072969 + 3 ^ 40 * 740897 * 2
def baseEnd_740897 : Nat := 380436276474292970780183

theorem tailTrace_740897 : CollatzResearch.WordTrace tailWord_740897 prefixEnd_740897 380436276474292970780183 := by
  unfold tailWord_740897
  simp only [CollatzResearch.WordTrace]
  refine ⟨27022733596864178978732945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18015155731242785985821963 27022733596864178978732945)
  ·
    refine ⟨20267050197648134234049709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27022733596864178978732945 20267050197648134234049709)
    ·
      refine ⟨7600143824118050337768641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20267050197648134234049709 7600143824118050337768641)
      ·
        refine ⟨5700107868088537753326481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7600143824118050337768641 5700107868088537753326481)
        ·
          refine ⟨4275080901066403314994861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5700107868088537753326481 4275080901066403314994861)
          ·
            refine ⟨1603155337899901243123073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4275080901066403314994861 1603155337899901243123073)
            ·
              refine ⟨1202366503424925932342305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603155337899901243123073 1202366503424925932342305)
              ·
                refine ⟨901774877568694449256729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202366503424925932342305 901774877568694449256729)
                ·
                  refine ⟨676331158176520836942547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 901774877568694449256729 676331158176520836942547)
                  ·
                    refine ⟨1014496737264781255413821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 676331158176520836942547 1014496737264781255413821)
                    ·
                      refine ⟨380436276474292970780183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014496737264781255413821 380436276474292970780183)
                      ·
                        rfl

theorem cell23_740897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_740897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740897 prefixEnd_740897 := by exact prefixLift 740897
  have htrace : WordTrace (prefixWord ++ tailWord_740897) baseStart_740897 baseEnd_740897 := by
    simpa [prefixWord, tailWord_740897, baseEnd_740897] using wordTrace_append hprefix tailTrace_740897
  have hstable : (prefixWord ++ tailWord_740897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740897).length < 2 ^ (prefixWord ++ tailWord_740897).sum := by decide
  have hdescent : baseEnd_740897 < baseStart_740897 := by decide
  rcases family_descends (prefixWord ++ tailWord_740897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740920 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 1, 4, 2]
def baseStart_740920 : Nat := 118140960795 + 740920 * 2 ^ 59
def prefixEnd_740920 : Nat := 4983230072969 + 3 ^ 40 * 740920 * 2
def baseEnd_740920 : Nat := 380448086529346380792577

theorem tailTrace_740920 : CollatzResearch.WordTrace tailWord_740920 prefixEnd_740920 380448086529346380792577 := by
  unfold tailWord_740920
  simp only [CollatzResearch.WordTrace]
  refine ⟨13511786237890426953410107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18015714983853902604546809 13511786237890426953410107)
  ·
    refine ⟨20267679356835640430115161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13511786237890426953410107 20267679356835640430115161)
    ·
      refine ⟨15200759517626730322586371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20267679356835640430115161 15200759517626730322586371)
      ·
        refine ⟨22801139276440095483879557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15200759517626730322586371 22801139276440095483879557)
        ·
          refine ⟨4275213614332517903227417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22801139276440095483879557 4275213614332517903227417)
          ·
            refine ⟨3206410210749388427420563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4275213614332517903227417 3206410210749388427420563)
            ·
              refine ⟨4809615316124082641130845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206410210749388427420563 4809615316124082641130845)
              ·
                refine ⟨1803605743546530990424067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4809615316124082641130845 1803605743546530990424067)
                ·
                  refine ⟨2705408615319796485636101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803605743546530990424067 2705408615319796485636101)
                  ·
                    refine ⟨507264115372461841056769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705408615319796485636101 507264115372461841056769)
                    ·
                      refine ⟨380448086529346380792577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507264115372461841056769 380448086529346380792577)
                      ·
                        rfl

theorem cell23_740920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_740920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740920 prefixEnd_740920 := by exact prefixLift 740920
  have htrace : WordTrace (prefixWord ++ tailWord_740920) baseStart_740920 baseEnd_740920 := by
    simpa [prefixWord, tailWord_740920, baseEnd_740920] using wordTrace_append hprefix tailTrace_740920
  have hstable : (prefixWord ++ tailWord_740920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740920).length < 2 ^ (prefixWord ++ tailWord_740920).sum := by decide
  have hdescent : baseEnd_740920 < baseStart_740920 := by decide
  rcases family_descends (prefixWord ++ tailWord_740920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740936 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_740936 : Nat := 118140960795 + 740936 * 2 ^ 59
def prefixEnd_740936 : Nat := 4983230072969 + 3 ^ 40 * 740936 * 2
def baseEnd_740936 : Nat := 380456302219818318192503

theorem tailTrace_740936 : CollatzResearch.WordTrace tailWord_740936 prefixEnd_740936 380456302219818318192503 := by
  unfold tailWord_740936
  simp only [CollatzResearch.WordTrace]
  refine ⟨13512078021861444319701331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18016104029148592426268441 13512078021861444319701331)
  ·
    refine ⟨20268117032792166479551997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13512078021861444319701331 20268117032792166479551997)
    ·
      refine ⟨7600543887297062429831999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20268117032792166479551997 7600543887297062429831999)
      ·
        refine ⟨11400815830945593644747999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7600543887297062429831999 11400815830945593644747999)
        ·
          refine ⟨17101223746418390467121999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11400815830945593644747999 17101223746418390467121999)
          ·
            refine ⟨25651835619627585700682999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17101223746418390467121999 25651835619627585700682999)
            ·
              refine ⟨38477753429441378551024499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25651835619627585700682999 38477753429441378551024499)
              ·
                refine ⟨57716630144162067826536749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38477753429441378551024499 57716630144162067826536749)
                ·
                  refine ⟨21643736304060775434951281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57716630144162067826536749 21643736304060775434951281)
                  ·
                    refine ⟨16232802228045581576213461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21643736304060775434951281 16232802228045581576213461)
                    ·
                      refine ⟨380456302219818318192503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16232802228045581576213461 380456302219818318192503)
                      ·
                        rfl

theorem cell23_740936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_740936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740936 prefixEnd_740936 := by exact prefixLift 740936
  have htrace : WordTrace (prefixWord ++ tailWord_740936) baseStart_740936 baseEnd_740936 := by
    simpa [prefixWord, tailWord_740936, baseEnd_740936] using wordTrace_append hprefix tailTrace_740936
  have hstable : (prefixWord ++ tailWord_740936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740936).length < 2 ^ (prefixWord ++ tailWord_740936).sum := by decide
  have hdescent : baseEnd_740936 < baseStart_740936 := by decide
  rcases family_descends (prefixWord ++ tailWord_740936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740970 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_740970 : Nat := 118140960795 + 740970 * 2 ^ 59
def prefixEnd_740970 : Nat := 4983230072969 + 3 ^ 40 * 740970 * 2
def baseEnd_740970 : Nat := 380473760562071185167347

theorem tailTrace_740970 : CollatzResearch.WordTrace tailWord_740970 prefixEnd_740970 380473760562071185167347 := by
  unfold tailWord_740970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6756349031399928111535091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18016930750399808297426909 6756349031399928111535091)
  ·
    refine ⟨10134523547099892167302637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6756349031399928111535091 10134523547099892167302637)
    ·
      refine ⟨3800446330162459562738489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10134523547099892167302637 3800446330162459562738489)
      ·
        refine ⟨2850334747621844672053867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3800446330162459562738489 2850334747621844672053867)
        ·
          refine ⟨4275502121432767008080801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850334747621844672053867 4275502121432767008080801)
          ·
            refine ⟨3206626591074575256060601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4275502121432767008080801 3206626591074575256060601)
            ·
              refine ⟨2404969943305931442045451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3206626591074575256060601 2404969943305931442045451)
              ·
                refine ⟨3607454914958897163068177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404969943305931442045451 3607454914958897163068177)
                ·
                  refine ⟨2705591186219172872301133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3607454914958897163068177 2705591186219172872301133)
                  ·
                    refine ⟨1014596694832189827112925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2705591186219172872301133 1014596694832189827112925)
                    ·
                      refine ⟨380473760562071185167347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014596694832189827112925 380473760562071185167347)
                      ·
                        rfl

theorem cell23_740970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_740970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_740970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_740970 prefixEnd_740970 := by exact prefixLift 740970
  have htrace : WordTrace (prefixWord ++ tailWord_740970) baseStart_740970 baseEnd_740970 := by
    simpa [prefixWord, tailWord_740970, baseEnd_740970] using wordTrace_append hprefix tailTrace_740970
  have hstable : (prefixWord ++ tailWord_740970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740970).length < 2 ^ (prefixWord ++ tailWord_740970).sum := by decide
  have hdescent : baseEnd_740970 < baseStart_740970 := by decide
  rcases family_descends (prefixWord ++ tailWord_740970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741047 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_741047 : Nat := 118140960795 + 741047 * 2 ^ 59
def prefixEnd_741047 : Nat := 4983230072969 + 3 ^ 40 * 741047 * 2
def baseEnd_741047 : Nat := 380513298572467383904493

theorem tailTrace_741047 : CollatzResearch.WordTrace tailWord_741047 prefixEnd_741047 380513298572467383904493 := by
  unfold tailWord_741047
  simp only [CollatzResearch.WordTrace]
  refine ⟨27028204546320754596693395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18018803030880503064462263 27028204546320754596693395)
  ·
    refine ⟨40542306819481131895040093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27028204546320754596693395 40542306819481131895040093)
    ·
      refine ⟨15203365057305424460640035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40542306819481131895040093 15203365057305424460640035)
      ·
        refine ⟨22805047585958136690960053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15203365057305424460640035 22805047585958136690960053)
        ·
          refine ⟨2137973211183575314777505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22805047585958136690960053 2137973211183575314777505)
          ·
            refine ⟨1603479908387681486083129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2137973211183575314777505 1603479908387681486083129)
            ·
              refine ⟨1202609931290761114562347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603479908387681486083129 1202609931290761114562347)
              ·
                refine ⟨1803914896936141671843521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202609931290761114562347 1803914896936141671843521)
                ·
                  refine ⟨1352936172702106253882641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803914896936141671843521 1352936172702106253882641)
                  ·
                    refine ⟨1014702129526579690411981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1352936172702106253882641 1014702129526579690411981)
                    ·
                      refine ⟨380513298572467383904493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014702129526579690411981 380513298572467383904493)
                      ·
                        rfl

theorem cell23_741047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_741047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741047 prefixEnd_741047 := by exact prefixLift 741047
  have htrace : WordTrace (prefixWord ++ tailWord_741047) baseStart_741047 baseEnd_741047 := by
    simpa [prefixWord, tailWord_741047, baseEnd_741047] using wordTrace_append hprefix tailTrace_741047
  have hstable : (prefixWord ++ tailWord_741047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741047).length < 2 ^ (prefixWord ++ tailWord_741047).sum := by decide
  have hdescent : baseEnd_741047 < baseStart_741047 := by decide
  rcases family_descends (prefixWord ++ tailWord_741047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741100 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_741100 : Nat := 118140960795 + 741100 * 2 ^ 59
def prefixEnd_741100 : Nat := 4983230072969 + 3 ^ 40 * 741100 * 2
def baseEnd_741100 : Nat := 380540513047155676541749

theorem tailTrace_741100 : CollatzResearch.WordTrace tailWord_741100 prefixEnd_741100 380540513047155676541749 := by
  unfold tailWord_741100
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515068807564372324186377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18020091743419163098915169 13515068807564372324186377)
  ·
    refine ⟨10136301605673279243139783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13515068807564372324186377 10136301605673279243139783)
    ·
      refine ⟨15204452408509918864709675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10136301605673279243139783 15204452408509918864709675)
      ·
        refine ⟨22806678612764878297064513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15204452408509918864709675 22806678612764878297064513)
        ·
          refine ⟨17105008959573658722798385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22806678612764878297064513 17105008959573658722798385)
          ·
            refine ⟨12828756719680244042098789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17105008959573658722798385 12828756719680244042098789)
            ·
              refine ⟨2405391884940045757893523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12828756719680244042098789 2405391884940045757893523)
              ·
                refine ⟨3608087827410068636840285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405391884940045757893523 3608087827410068636840285)
                ·
                  refine ⟨1353032935278775738815107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3608087827410068636840285 1353032935278775738815107)
                  ·
                    refine ⟨2029549402918163608222661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1353032935278775738815107 2029549402918163608222661)
                    ·
                      refine ⟨380540513047155676541749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2029549402918163608222661 380540513047155676541749)
                      ·
                        rfl

theorem cell23_741100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_741100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741100 prefixEnd_741100 := by exact prefixLift 741100
  have htrace : WordTrace (prefixWord ++ tailWord_741100) baseStart_741100 baseEnd_741100 := by
    simpa [prefixWord, tailWord_741100, baseEnd_741100] using wordTrace_append hprefix tailTrace_741100
  have hstable : (prefixWord ++ tailWord_741100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741100).length < 2 ^ (prefixWord ++ tailWord_741100).sum := by decide
  have hdescent : baseEnd_741100 < baseStart_741100 := by decide
  rcases family_descends (prefixWord ++ tailWord_741100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741113 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_741113 : Nat := 118140960795 + 741113 * 2 ^ 59
def prefixEnd_741113 : Nat := 4983230072969 + 3 ^ 40 * 741113 * 2
def baseEnd_741113 : Nat := 380547188295664125679189

theorem tailTrace_741113 : CollatzResearch.WordTrace tailWord_741113 prefixEnd_741113 380547188295664125679189 := by
  unfold tailWord_741113
  simp only [CollatzResearch.WordTrace]
  refine ⟨27030611764081647868595993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18020407842721098579063995 27030611764081647868595993)
  ·
    refine ⟨20272958823061235901446995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27030611764081647868595993 20272958823061235901446995)
    ·
      refine ⟨30409438234591853852170493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20272958823061235901446995 30409438234591853852170493)
      ·
        refine ⟨11403539337971945194563935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30409438234591853852170493 11403539337971945194563935)
        ·
          refine ⟨17105309006957917791845903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11403539337971945194563935 17105309006957917791845903)
          ·
            refine ⟨25657963510436876687768855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17105309006957917791845903 25657963510436876687768855)
            ·
              refine ⟨38486945265655315031653283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25657963510436876687768855 38486945265655315031653283)
              ·
                refine ⟨57730417898482972547479925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38486945265655315031653283 57730417898482972547479925)
                ·
                  refine ⟨5412226677982778676326243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57730417898482972547479925 5412226677982778676326243)
                  ·
                    refine ⟨8118340016974168014489365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5412226677982778676326243 8118340016974168014489365)
                    ·
                      refine ⟨380547188295664125679189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8118340016974168014489365 380547188295664125679189)
                      ·
                        rfl

theorem cell23_741113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_741113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741113 prefixEnd_741113 := by exact prefixLift 741113
  have htrace : WordTrace (prefixWord ++ tailWord_741113) baseStart_741113 baseEnd_741113 := by
    simpa [prefixWord, tailWord_741113, baseEnd_741113] using wordTrace_append hprefix tailTrace_741113
  have hstable : (prefixWord ++ tailWord_741113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741113).length < 2 ^ (prefixWord ++ tailWord_741113).sum := by decide
  have hdescent : baseEnd_741113 < baseStart_741113 := by decide
  rcases family_descends (prefixWord ++ tailWord_741113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741134 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_741134 : Nat := 118140960795 + 741134 * 2 ^ 59
def prefixEnd_741134 : Nat := 4983230072969 + 3 ^ 40 * 741134 * 2
def baseEnd_741134 : Nat := 380557971389408543516593

theorem tailTrace_741134 : CollatzResearch.WordTrace tailWord_741134 prefixEnd_741134 380557971389408543516593 := by
  unfold tailWord_741134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378922212125696056888807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18020918464670378970073637 3378922212125696056888807)
  ·
    refine ⟨5068383318188544085333211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3378922212125696056888807 5068383318188544085333211)
    ·
      refine ⟨7602574977282816127999817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5068383318188544085333211 7602574977282816127999817)
      ·
        refine ⟨5701931232962112095999863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7602574977282816127999817 5701931232962112095999863)
        ·
          refine ⟨8552896849443168143999795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701931232962112095999863 8552896849443168143999795)
          ·
            refine ⟨12829345274164752215999693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552896849443168143999795 12829345274164752215999693)
            ·
              refine ⟨4811004477811782080999885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12829345274164752215999693 4811004477811782080999885)
              ·
                refine ⟨1804126679179418280374957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4811004477811782080999885 1804126679179418280374957)
                ·
                  refine ⟨676547504692281855140609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1804126679179418280374957 676547504692281855140609)
                  ·
                    refine ⟨507410628519211391355457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 676547504692281855140609 507410628519211391355457)
                    ·
                      refine ⟨380557971389408543516593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507410628519211391355457 380557971389408543516593)
                      ·
                        rfl

theorem cell23_741134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_741134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741134 prefixEnd_741134 := by exact prefixLift 741134
  have htrace : WordTrace (prefixWord ++ tailWord_741134) baseStart_741134 baseEnd_741134 := by
    simpa [prefixWord, tailWord_741134, baseEnd_741134] using wordTrace_append hprefix tailTrace_741134
  have hstable : (prefixWord ++ tailWord_741134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741134).length < 2 ^ (prefixWord ++ tailWord_741134).sum := by decide
  have hdescent : baseEnd_741134 < baseStart_741134 := by decide
  rcases family_descends (prefixWord ++ tailWord_741134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741154 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_741154 : Nat := 118140960795 + 741154 * 2 ^ 59
def prefixEnd_741154 : Nat := 4983230072969 + 3 ^ 40 * 741154 * 2
def baseEnd_741154 : Nat := 380568241002498465266501

theorem tailTrace_741154 : CollatzResearch.WordTrace tailWord_741154 prefixEnd_741154 380568241002498465266501 := by
  unfold tailWord_741154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758026789233277967709629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18021404771288741247225677 6758026789233277967709629)
  ·
    refine ⟨2534260045962479237891111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6758026789233277967709629 2534260045962479237891111)
    ·
      refine ⟨3801390068943718856836667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534260045962479237891111 3801390068943718856836667)
      ·
        refine ⟨5702085103415578285255001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801390068943718856836667 5702085103415578285255001)
        ·
          refine ⟨4276563827561683713941251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5702085103415578285255001 4276563827561683713941251)
          ·
            refine ⟨6414845741342525570911877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276563827561683713941251 6414845741342525570911877)
            ·
              refine ⟨1202783576501723544545977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6414845741342525570911877 1202783576501723544545977)
              ·
                refine ⟨902087682376292658409483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202783576501723544545977 902087682376292658409483)
                ·
                  refine ⟨1353131523564438987614225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902087682376292658409483 1353131523564438987614225)
                  ·
                    refine ⟨1014848642673329240710669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353131523564438987614225 1014848642673329240710669)
                    ·
                      refine ⟨380568241002498465266501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014848642673329240710669 380568241002498465266501)
                      ·
                        rfl

theorem cell23_741154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_741154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741154 prefixEnd_741154 := by exact prefixLift 741154
  have htrace : WordTrace (prefixWord ++ tailWord_741154) baseStart_741154 baseEnd_741154 := by
    simpa [prefixWord, tailWord_741154, baseEnd_741154] using wordTrace_append hprefix tailTrace_741154
  have hstable : (prefixWord ++ tailWord_741154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741154).length < 2 ^ (prefixWord ++ tailWord_741154).sum := by decide
  have hdescent : baseEnd_741154 < baseStart_741154 := by decide
  rcases family_descends (prefixWord ++ tailWord_741154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741157 : List Nat := [1, 3, 1, 2, 3, 4, 2, 7]
def baseStart_741157 : Nat := 118140960795 + 741157 * 2 ^ 59
def prefixEnd_741157 : Nat := 4983230072969 + 3 ^ 40 * 741157 * 2
def baseEnd_741157 : Nat := 14095177090535627908481

theorem tailTrace_741157 : CollatzResearch.WordTrace tailWord_741157 prefixEnd_741157 14095177090535627908481 := by
  unfold tailWord_741157
  simp only [CollatzResearch.WordTrace]
  refine ⟨27032216575922243383197725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18021477717281495588798483 27032216575922243383197725)
  ·
    refine ⟨10137081215970841268699147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27032216575922243383197725 10137081215970841268699147)
    ·
      refine ⟨15205621823956261903048721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10137081215970841268699147 15205621823956261903048721)
      ·
        refine ⟨11404216367967196427286541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15205621823956261903048721 11404216367967196427286541)
        ·
          refine ⟨4276581137987698660232453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11404216367967196427286541 4276581137987698660232453)
          ·
            refine ⟨801858963372693498793585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4276581137987698660232453 801858963372693498793585)
            ·
              refine ⟨601394222529520124095189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801858963372693498793585 601394222529520124095189)
              ·
                refine ⟨14095177090535627908481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 601394222529520124095189 14095177090535627908481)
                ·
                  rfl

theorem cell23_741157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 7].length) (baseStart_741157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741157 prefixEnd_741157 := by exact prefixLift 741157
  have htrace : WordTrace (prefixWord ++ tailWord_741157) baseStart_741157 baseEnd_741157 := by
    simpa [prefixWord, tailWord_741157, baseEnd_741157] using wordTrace_append hprefix tailTrace_741157
  have hstable : (prefixWord ++ tailWord_741157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741157).length < 2 ^ (prefixWord ++ tailWord_741157).sum := by decide
  have hdescent : baseEnd_741157 < baseStart_741157 := by decide
  rcases family_descends (prefixWord ++ tailWord_741157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741163 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 7]
def baseStart_741163 : Nat := 118140960795 + 741163 * 2 ^ 59
def prefixEnd_741163 : Nat := 4983230072969 + 3 ^ 40 * 741163 * 2
def baseEnd_741163 : Nat := 380572862328388930053959

theorem tailTrace_741163 : CollatzResearch.WordTrace tailWord_741163 prefixEnd_741163 380572862328388930053959 := by
  unfold tailWord_741163
  simp only [CollatzResearch.WordTrace]
  refine ⟨27032435413900506407916143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18021623609267004271944095 27032435413900506407916143)
  ·
    refine ⟨40548653120850759611874215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27032435413900506407916143 40548653120850759611874215)
    ·
      refine ⟨60822979681276139417811323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40548653120850759611874215 60822979681276139417811323)
      ·
        refine ⟨91234469521914209126716985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60822979681276139417811323 91234469521914209126716985)
        ·
          refine ⟨68425852141435656845037739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91234469521914209126716985 68425852141435656845037739)
          ·
            refine ⟨102638778212153485267556609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68425852141435656845037739 102638778212153485267556609)
            ·
              refine ⟨76979083659115113950667457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102638778212153485267556609 76979083659115113950667457)
              ·
                refine ⟨57734312744336335463000593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76979083659115113950667457 57734312744336335463000593)
                ·
                  refine ⟨43300734558252251597250445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57734312744336335463000593 43300734558252251597250445)
                  ·
                    refine ⟨16237775459344594348968917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43300734558252251597250445 16237775459344594348968917)
                    ·
                      refine ⟨380572862328388930053959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16237775459344594348968917 380572862328388930053959)
                      ·
                        rfl

theorem cell23_741163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 7].length) (baseStart_741163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741163 prefixEnd_741163 := by exact prefixLift 741163
  have htrace : WordTrace (prefixWord ++ tailWord_741163) baseStart_741163 baseEnd_741163 := by
    simpa [prefixWord, tailWord_741163, baseEnd_741163] using wordTrace_append hprefix tailTrace_741163
  have hstable : (prefixWord ++ tailWord_741163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741163).length < 2 ^ (prefixWord ++ tailWord_741163).sum := by decide
  have hdescent : baseEnd_741163 < baseStart_741163 := by decide
  rcases family_descends (prefixWord ++ tailWord_741163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741201 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 2, 1, 3]
def baseStart_741201 : Nat := 118140960795 + 741201 * 2 ^ 59
def prefixEnd_741201 : Nat := 4983230072969 + 3 ^ 40 * 741201 * 2
def baseEnd_741201 : Nat := 380592374593259781378785

theorem tailTrace_741201 : CollatzResearch.WordTrace tailWord_741201 prefixEnd_741201 380592374593259781378785 := by
  unfold tailWord_741201
  simp only [CollatzResearch.WordTrace]
  refine ⟨27033821387762838897799457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18022547591841892598532971 27033821387762838897799457)
  ·
    refine ⟨20275366040822129173349593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27033821387762838897799457 20275366040822129173349593)
    ·
      refine ⟨15206524530616596880012195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20275366040822129173349593 15206524530616596880012195)
      ·
        refine ⟨22809786795924895320018293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15206524530616596880012195 22809786795924895320018293)
        ·
          refine ⟨2138417512117958936251715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22809786795924895320018293 2138417512117958936251715)
          ·
            refine ⟨3207626268176938404377573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138417512117958936251715 3207626268176938404377573)
            ·
              refine ⟨601429925283175950820795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3207626268176938404377573 601429925283175950820795)
              ·
                refine ⟨902144887924763926231193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601429925283175950820795 902144887924763926231193)
                ·
                  refine ⟨676608665943572944673395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 902144887924763926231193 676608665943572944673395)
                  ·
                    refine ⟨1014912998915359417010093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 676608665943572944673395 1014912998915359417010093)
                    ·
                      refine ⟨380592374593259781378785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014912998915359417010093 380592374593259781378785)
                      ·
                        rfl

theorem cell23_741201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_741201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741201 prefixEnd_741201 := by exact prefixLift 741201
  have htrace : WordTrace (prefixWord ++ tailWord_741201) baseStart_741201 baseEnd_741201 := by
    simpa [prefixWord, tailWord_741201, baseEnd_741201] using wordTrace_append hprefix tailTrace_741201
  have hstable : (prefixWord ++ tailWord_741201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741201).length < 2 ^ (prefixWord ++ tailWord_741201).sum := by decide
  have hdescent : baseEnd_741201 < baseStart_741201 := by decide
  rcases family_descends (prefixWord ++ tailWord_741201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741210 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_741210 : Nat := 118140960795 + 741210 * 2 ^ 59
def prefixEnd_741210 : Nat := 4983230072969 + 3 ^ 40 * 741210 * 2
def baseEnd_741210 : Nat := 380596995919150246166243

theorem tailTrace_741210 : CollatzResearch.WordTrace tailWord_741210 prefixEnd_741210 380596995919150246166243 := by
  unfold tailWord_741210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758537411182558358719271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18022766429820155623251389 6758537411182558358719271)
  ·
    refine ⟨10137806116773837538078907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6758537411182558358719271 10137806116773837538078907)
    ·
      refine ⟨15206709175160756307118361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10137806116773837538078907 15206709175160756307118361)
      ·
        refine ⟨11405031881370567230338771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15206709175160756307118361 11405031881370567230338771)
        ·
          refine ⟨17107547822055850845508157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405031881370567230338771 17107547822055850845508157)
          ·
            refine ⟨6415330433270944067065559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17107547822055850845508157 6415330433270944067065559)
            ·
              refine ⟨9622995649906416100598339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415330433270944067065559 9622995649906416100598339)
              ·
                refine ⟨14434493474859624150897509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9622995649906416100598339 14434493474859624150897509)
                ·
                  refine ⟨2706467526536179528293283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14434493474859624150897509 2706467526536179528293283)
                  ·
                    refine ⟨4059701289804269292439925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2706467526536179528293283 4059701289804269292439925)
                    ·
                      refine ⟨380596995919150246166243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4059701289804269292439925 380596995919150246166243)
                      ·
                        rfl

theorem cell23_741210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_741210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741210 prefixEnd_741210 := by exact prefixLift 741210
  have htrace : WordTrace (prefixWord ++ tailWord_741210) baseStart_741210 baseEnd_741210 := by
    simpa [prefixWord, tailWord_741210, baseEnd_741210] using wordTrace_append hprefix tailTrace_741210
  have hstable : (prefixWord ++ tailWord_741210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741210).length < 2 ^ (prefixWord ++ tailWord_741210).sum := by decide
  have hdescent : baseEnd_741210 < baseStart_741210 := by decide
  rcases family_descends (prefixWord ++ tailWord_741210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741224 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_741224 : Nat := 118140960795 + 741224 * 2 ^ 59
def prefixEnd_741224 : Nat := 4983230072969 + 3 ^ 40 * 741224 * 2
def baseEnd_741224 : Nat := 380604184648313191391179

theorem tailTrace_741224 : CollatzResearch.WordTrace tailWord_741224 prefixEnd_741224 380604184648313191391179 := by
  unfold tailWord_741224
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517330133339756912943363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18023106844453009217257817 13517330133339756912943363)
  ·
    refine ⟨20275995200009635369415045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13517330133339756912943363 20275995200009635369415045)
    ·
      refine ⟨3801749100001806631765321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20275995200009635369415045 3801749100001806631765321)
      ·
        refine ⟨2851311825001354973823991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3801749100001806631765321 2851311825001354973823991)
        ·
          refine ⟨4276967737502032460735987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851311825001354973823991 4276967737502032460735987)
          ·
            refine ⟨6415451606253048691103981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276967737502032460735987 6415451606253048691103981)
            ·
              refine ⟨2405794352344893259163993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6415451606253048691103981 2405794352344893259163993)
              ·
                refine ⟨1804345764258669944372995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2405794352344893259163993 1804345764258669944372995)
                ·
                  refine ⟨2706518646388004916559493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804345764258669944372995 2706518646388004916559493)
                  ·
                    refine ⟨507472246197750921854905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2706518646388004916559493 507472246197750921854905)
                    ·
                      refine ⟨380604184648313191391179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507472246197750921854905 380604184648313191391179)
                      ·
                        rfl

theorem cell23_741224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_741224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741224 prefixEnd_741224 := by exact prefixLift 741224
  have htrace : WordTrace (prefixWord ++ tailWord_741224) baseStart_741224 baseEnd_741224 := by
    simpa [prefixWord, tailWord_741224, baseEnd_741224] using wordTrace_append hprefix tailTrace_741224
  have hstable : (prefixWord ++ tailWord_741224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741224).length < 2 ^ (prefixWord ++ tailWord_741224).sum := by decide
  have hdescent : baseEnd_741224 < baseStart_741224 := by decide
  rcases family_descends (prefixWord ++ tailWord_741224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741237 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_741237 : Nat := 118140960795 + 741237 * 2 ^ 59
def prefixEnd_741237 : Nat := 4983230072969 + 3 ^ 40 * 741237 * 2
def baseEnd_741237 : Nat := 380610859896821640528619

theorem tailTrace_741237 : CollatzResearch.WordTrace tailWord_741237 prefixEnd_741237 380610859896821640528619 := by
  unfold tailWord_741237
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035134415632417046109965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18023422943754944697406643 27035134415632417046109965)
  ·
    refine ⟨10138175405862156392291237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27035134415632417046109965 10138175405862156392291237)
    ·
      refine ⟨1900907888599154323554607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10138175405862156392291237 1900907888599154323554607)
      ·
        refine ⟨2851361832898731485331911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900907888599154323554607 2851361832898731485331911)
        ·
          refine ⟨4277042749348097227997867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851361832898731485331911 4277042749348097227997867)
          ·
            refine ⟨6415564124022145841996801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277042749348097227997867 6415564124022145841996801)
            ·
              refine ⟨4811673093016609381497601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6415564124022145841996801 4811673093016609381497601)
              ·
                refine ⟨3608754819762457036123201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811673093016609381497601 3608754819762457036123201)
                ·
                  refine ⟨2706566114821842777092401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608754819762457036123201 2706566114821842777092401)
                  ·
                    refine ⟨2029924586116382082819301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2706566114821842777092401 2029924586116382082819301)
                    ·
                      refine ⟨380610859896821640528619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2029924586116382082819301 380610859896821640528619)
                      ·
                        rfl

theorem cell23_741237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_741237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741237 prefixEnd_741237 := by exact prefixLift 741237
  have htrace : WordTrace (prefixWord ++ tailWord_741237) baseStart_741237 baseEnd_741237 := by
    simpa [prefixWord, tailWord_741237, baseEnd_741237] using wordTrace_append hprefix tailTrace_741237
  have hstable : (prefixWord ++ tailWord_741237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741237).length < 2 ^ (prefixWord ++ tailWord_741237).sum := by decide
  have hdescent : baseEnd_741237 < baseStart_741237 := by decide
  rcases family_descends (prefixWord ++ tailWord_741237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741241 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 2, 2, 2]
def baseStart_741241 : Nat := 118140960795 + 741241 * 2 ^ 59
def prefixEnd_741241 : Nat := 4983230072969 + 3 ^ 40 * 741241 * 2
def baseEnd_741241 : Nat := 380612913819439624878601

theorem tailTrace_741241 : CollatzResearch.WordTrace tailWord_741241 prefixEnd_741241 380612913819439624878601 := by
  unfold tailWord_741241
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035280307617925729255577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18023520205078617152837051 27035280307617925729255577)
  ·
    refine ⟨20276460230713444296941683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27035280307617925729255577 20276460230713444296941683)
    ·
      refine ⟨30414690346070166445412525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20276460230713444296941683 30414690346070166445412525)
      ·
        refine ⟨11405508879776312417029697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30414690346070166445412525 11405508879776312417029697)
        ·
          refine ⟨8554131659832234312772273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11405508879776312417029697 8554131659832234312772273)
          ·
            refine ⟨6415598744874175734579205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8554131659832234312772273 6415598744874175734579205)
            ·
              refine ⟨1202924764663907950233601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6415598744874175734579205 1202924764663907950233601)
              ·
                refine ⟨902193573497930962675201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202924764663907950233601 902193573497930962675201)
                ·
                  refine ⟨676645180123448222006401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 902193573497930962675201 676645180123448222006401)
                  ·
                    refine ⟨507483885092586166504801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 676645180123448222006401 507483885092586166504801)
                    ·
                      refine ⟨380612913819439624878601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507483885092586166504801 380612913819439624878601)
                      ·
                        rfl

theorem cell23_741241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_741241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741241 prefixEnd_741241 := by exact prefixLift 741241
  have htrace : WordTrace (prefixWord ++ tailWord_741241) baseStart_741241 baseEnd_741241 := by
    simpa [prefixWord, tailWord_741241, baseEnd_741241] using wordTrace_append hprefix tailTrace_741241
  have hstable : (prefixWord ++ tailWord_741241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741241).length < 2 ^ (prefixWord ++ tailWord_741241).sum := by decide
  have hdescent : baseEnd_741241 < baseStart_741241 := by decide
  rcases family_descends (prefixWord ++ tailWord_741241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741257 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 3]
def baseStart_741257 : Nat := 118140960795 + 741257 * 2 ^ 59
def prefixEnd_741257 : Nat := 4983230072969 + 3 ^ 40 * 741257 * 2
def baseEnd_741257 : Nat := 380621129509911562278527

theorem tailTrace_741257 : CollatzResearch.WordTrace tailWord_741257 prefixEnd_741257 380621129509911562278527 := by
  unfold tailWord_741257
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035863875559960461838025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18023909250373306974558683 27035863875559960461838025)
  ·
    refine ⟨20276897906669970346378519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27035863875559960461838025 20276897906669970346378519)
    ·
      refine ⟨30415346860004955519567779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20276897906669970346378519 30415346860004955519567779)
      ·
        refine ⟨45623020290007433279351669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30415346860004955519567779 45623020290007433279351669)
        ·
          refine ⟨4277158152188196869939219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45623020290007433279351669 4277158152188196869939219)
          ·
            refine ⟨6415737228282295304908829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277158152188196869939219 6415737228282295304908829)
            ·
              refine ⟨2405901460605860739340811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6415737228282295304908829 2405901460605860739340811)
              ·
                refine ⟨3608852190908791109011217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405901460605860739340811 3608852190908791109011217)
                ·
                  refine ⟨2706639143181593331758413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608852190908791109011217 2706639143181593331758413)
                  ·
                    refine ⟨1014989678693097499409405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2706639143181593331758413 1014989678693097499409405)
                    ·
                      refine ⟨380621129509911562278527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1014989678693097499409405 380621129509911562278527)
                      ·
                        rfl

theorem cell23_741257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_741257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741257 prefixEnd_741257 := by exact prefixLift 741257
  have htrace : WordTrace (prefixWord ++ tailWord_741257) baseStart_741257 baseEnd_741257 := by
    simpa [prefixWord, tailWord_741257, baseEnd_741257] using wordTrace_append hprefix tailTrace_741257
  have hstable : (prefixWord ++ tailWord_741257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741257).length < 2 ^ (prefixWord ++ tailWord_741257).sum := by decide
  have hdescent : baseEnd_741257 < baseStart_741257 := by decide
  rcases family_descends (prefixWord ++ tailWord_741257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741260 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_741260 : Nat := 118140960795 + 741260 * 2 ^ 59
def prefixEnd_741260 : Nat := 4983230072969 + 3 ^ 40 * 741260 * 2
def baseEnd_741260 : Nat := 126874223317291683513671

theorem tailTrace_741260 : CollatzResearch.WordTrace tailWord_741260 prefixEnd_741260 126874223317291683513671 := by
  unfold tailWord_741260
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517986647274545987098617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18023982196366061316131489 13517986647274545987098617)
  ·
    refine ⟨10138489985455909490323963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13517986647274545987098617 10138489985455909490323963)
    ·
      refine ⟨15207734978183864235485945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10138489985455909490323963 15207734978183864235485945)
      ·
        refine ⟨11405801233637898176614459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15207734978183864235485945 11405801233637898176614459)
        ·
          refine ⟨17108701850456847264921689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405801233637898176614459 17108701850456847264921689)
          ·
            refine ⟨12831526387842635448691267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17108701850456847264921689 12831526387842635448691267)
            ·
              refine ⟨19247289581763953173036901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12831526387842635448691267 19247289581763953173036901)
              ·
                refine ⟨3608866796580741219944419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19247289581763953173036901 3608866796580741219944419)
                ·
                  refine ⟨5413300194871111829916629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608866796580741219944419 5413300194871111829916629)
                  ·
                    refine ⟨126874223317291683513671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5413300194871111829916629 126874223317291683513671)
                    ·
                      rfl

theorem cell23_741260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_741260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741260 prefixEnd_741260 := by exact prefixLift 741260
  have htrace : WordTrace (prefixWord ++ tailWord_741260) baseStart_741260 baseEnd_741260 := by
    simpa [prefixWord, tailWord_741260, baseEnd_741260] using wordTrace_append hprefix tailTrace_741260
  have hstable : (prefixWord ++ tailWord_741260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741260).length < 2 ^ (prefixWord ++ tailWord_741260).sum := by decide
  have hdescent : baseEnd_741260 < baseStart_741260 := by decide
  rcases family_descends (prefixWord ++ tailWord_741260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741277 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_741277 : Nat := 118140960795 + 741277 * 2 ^ 59
def prefixEnd_741277 : Nat := 4983230072969 + 3 ^ 40 * 741277 * 2
def baseEnd_741277 : Nat := 126877133041000494676145

theorem tailTrace_741277 : CollatzResearch.WordTrace tailWord_741277 prefixEnd_741277 126877133041000494676145 := by
  unfold tailWord_741277
  simp only [CollatzResearch.WordTrace]
  refine ⟨27036593335487503877566085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18024395556991669251710723 27036593335487503877566085)
  ·
    refine ⟨5069361250403906977043641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27036593335487503877566085 5069361250403906977043641)
    ·
      refine ⟨3802020937802930232782731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5069361250403906977043641 3802020937802930232782731)
      ·
        refine ⟨5703031406704395349174097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3802020937802930232782731 5703031406704395349174097)
        ·
          refine ⟨4277273555028296511880573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5703031406704395349174097 4277273555028296511880573)
          ·
            refine ⟨1603977583135611191955215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4277273555028296511880573 1603977583135611191955215)
            ·
              refine ⟨2405966374703416787932823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603977583135611191955215 2405966374703416787932823)
              ·
                refine ⟨3608949562055125181899235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405966374703416787932823 3608949562055125181899235)
                ·
                  refine ⟨5413424343082687772848853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608949562055125181899235 5413424343082687772848853)
                  ·
                    refine ⟨126877133041000494676145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5413424343082687772848853 126877133041000494676145)
                    ·
                      rfl

theorem cell23_741277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_741277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741277 prefixEnd_741277 := by exact prefixLift 741277
  have htrace : WordTrace (prefixWord ++ tailWord_741277) baseStart_741277 baseEnd_741277 := by
    simpa [prefixWord, tailWord_741277, baseEnd_741277] using wordTrace_append hprefix tailTrace_741277
  have hstable : (prefixWord ++ tailWord_741277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741277).length < 2 ^ (prefixWord ++ tailWord_741277).sum := by decide
  have hdescent : baseEnd_741277 < baseStart_741277 := by decide
  rcases family_descends (prefixWord ++ tailWord_741277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741281 : List Nat := [1, 2, 3, 4, 2, 1, 2, 3, 5]
def baseStart_741281 : Nat := 118140960795 + 741281 * 2 ^ 59
def prefixEnd_741281 : Nat := 4983230072969 + 3 ^ 40 * 741281 * 2
def baseEnd_741281 : Nat := 42292605893957718708713

theorem tailTrace_741281 : CollatzResearch.WordTrace tailWord_741281 prefixEnd_741281 42292605893957718708713 := by
  unfold tailWord_741281
  simp only [CollatzResearch.WordTrace]
  refine ⟨27036739227473012560711697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18024492818315341707141131 27036739227473012560711697)
  ·
    refine ⟨20277554420604759420533773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27036739227473012560711697 20277554420604759420533773)
    ·
      refine ⟨7604082907726784782700165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20277554420604759420533773 7604082907726784782700165)
      ·
        refine ⟨1425765545198772146756281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7604082907726784782700165 1425765545198772146756281)
        ·
          refine ⟨1069324158899079110067211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425765545198772146756281 1069324158899079110067211)
          ·
            refine ⟨1603986238348618665100817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069324158899079110067211 1603986238348618665100817)
            ·
              refine ⟨1202989678761463998825613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603986238348618665100817 1202989678761463998825613)
              ·
                refine ⟨451121129535548999559605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1202989678761463998825613 451121129535548999559605)
                ·
                  refine ⟨42292605893957718708713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 451121129535548999559605 42292605893957718708713)
                  ·
                    rfl

theorem cell23_741281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 5].length) (baseStart_741281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741281 prefixEnd_741281 := by exact prefixLift 741281
  have htrace : WordTrace (prefixWord ++ tailWord_741281) baseStart_741281 baseEnd_741281 := by
    simpa [prefixWord, tailWord_741281, baseEnd_741281] using wordTrace_append hprefix tailTrace_741281
  have hstable : (prefixWord ++ tailWord_741281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741281).length < 2 ^ (prefixWord ++ tailWord_741281).sum := by decide
  have hdescent : baseEnd_741281 < baseStart_741281 := by decide
  rcases family_descends (prefixWord ++ tailWord_741281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741307 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 3, 4]
def baseStart_741307 : Nat := 118140960795 + 741307 * 2 ^ 59
def prefixEnd_741307 : Nat := 4983230072969 + 3 ^ 40 * 741307 * 2
def baseEnd_741307 : Nat := 126882267847545455551099

theorem tailTrace_741307 : CollatzResearch.WordTrace tailWord_741307 prefixEnd_741307 126882267847545455551099 := by
  unfold tailWord_741307
  simp only [CollatzResearch.WordTrace]
  refine ⟨27037687525378819001158175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18025125016919212667438783 27037687525378819001158175)
  ·
    refine ⟨40556531288068228501737263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27037687525378819001158175 40556531288068228501737263)
    ·
      refine ⟨60834796932102342752605895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40556531288068228501737263 60834796932102342752605895)
      ·
        refine ⟨91252195398153514128908843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60834796932102342752605895 91252195398153514128908843)
        ·
          refine ⟨136878293097230271193363265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91252195398153514128908843 136878293097230271193363265)
          ·
            refine ⟨102658719822922703395022449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136878293097230271193363265 102658719822922703395022449)
            ·
              refine ⟨76994039867192027546266837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102658719822922703395022449 76994039867192027546266837)
              ·
                refine ⟨1804547809387313145615629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76994039867192027546266837 1804547809387313145615629)
                ·
                  refine ⟨676705428520242429605861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1804547809387313145615629 676705428520242429605861)
                  ·
                    refine ⟨126882267847545455551099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 676705428520242429605861 126882267847545455551099)
                    ·
                      rfl

theorem cell23_741307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 4].length) (baseStart_741307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741307 prefixEnd_741307 := by exact prefixLift 741307
  have htrace : WordTrace (prefixWord ++ tailWord_741307) baseStart_741307 baseEnd_741307 := by
    simpa [prefixWord, tailWord_741307, baseEnd_741307] using wordTrace_append hprefix tailTrace_741307
  have hstable : (prefixWord ++ tailWord_741307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741307).length < 2 ^ (prefixWord ++ tailWord_741307).sum := by decide
  have hdescent : baseEnd_741307 < baseStart_741307 := by decide
  rcases family_descends (prefixWord ++ tailWord_741307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741317 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_741317 : Nat := 118140960795 + 741317 * 2 ^ 59
def prefixEnd_741317 : Nat := 4983230072969 + 3 ^ 40 * 741317 * 2
def baseEnd_741317 : Nat := 380651938349181327528251

theorem tailTrace_741317 : CollatzResearch.WordTrace tailWord_741317 prefixEnd_741317 380651938349181327528251 := by
  unfold tailWord_741317
  simp only [CollatzResearch.WordTrace]
  refine ⟨27038052255342590709022205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18025368170228393806014803 27038052255342590709022205)
  ·
    refine ⟨10139269595753471515883327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27038052255342590709022205 10139269595753471515883327)
    ·
      refine ⟨15208904393630207273824991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10139269595753471515883327 15208904393630207273824991)
      ·
        refine ⟨22813356590445310910737487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15208904393630207273824991 22813356590445310910737487)
        ·
          refine ⟨34220034885667966366106231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22813356590445310910737487 34220034885667966366106231)
          ·
            refine ⟨51330052328501949549159347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34220034885667966366106231 51330052328501949549159347)
            ·
              refine ⟨76995078492752924323739021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51330052328501949549159347 76995078492752924323739021)
              ·
                refine ⟨28873154434782346621402133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76995078492752924323739021 28873154434782346621402133)
                ·
                  refine ⟨1353429114130422497878225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28873154434782346621402133 1353429114130422497878225)
                  ·
                    refine ⟨1015071835597816873408669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353429114130422497878225 1015071835597816873408669)
                    ·
                      refine ⟨380651938349181327528251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1015071835597816873408669 380651938349181327528251)
                      ·
                        rfl

theorem cell23_741317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_741317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741317 prefixEnd_741317 := by exact prefixLift 741317
  have htrace : WordTrace (prefixWord ++ tailWord_741317) baseStart_741317 baseEnd_741317 := by
    simpa [prefixWord, tailWord_741317, baseEnd_741317] using wordTrace_append hprefix tailTrace_741317
  have hstable : (prefixWord ++ tailWord_741317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741317).length < 2 ^ (prefixWord ++ tailWord_741317).sum := by decide
  have hdescent : baseEnd_741317 < baseStart_741317 := by decide
  rcases family_descends (prefixWord ++ tailWord_741317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741324 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_741324 : Nat := 118140960795 + 741324 * 2 ^ 59
def prefixEnd_741324 : Nat := 4983230072969 + 3 ^ 40 * 741324 * 2
def baseEnd_741324 : Nat := 126885177571254266713573

theorem tailTrace_741324 : CollatzResearch.WordTrace tailWord_741324 prefixEnd_741324 126885177571254266713573 := by
  unfold tailWord_741324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13519153783158615452263513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18025538377544820603018017 13519153783158615452263513)
  ·
    refine ⟨10139365337368961589197635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13519153783158615452263513 10139365337368961589197635)
    ·
      refine ⟨15209048006053442383796453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10139365337368961589197635 15209048006053442383796453)
      ·
        refine ⟨2851696501135020446961835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15209048006053442383796453 2851696501135020446961835)
        ·
          refine ⟨4277544751702530670442753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851696501135020446961835 4277544751702530670442753)
          ·
            refine ⟨3208158563776898002832065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4277544751702530670442753 3208158563776898002832065)
            ·
              refine ⟨2406118922832673502124049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3208158563776898002832065 2406118922832673502124049)
              ·
                refine ⟨1804589192124505126593037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406118922832673502124049 1804589192124505126593037)
                ·
                  refine ⟨676720947046689422472389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1804589192124505126593037 676720947046689422472389)
                  ·
                    refine ⟨126885177571254266713573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 676720947046689422472389 126885177571254266713573)
                    ·
                      rfl

theorem cell23_741324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_741324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741324 prefixEnd_741324 := by exact prefixLift 741324
  have htrace : WordTrace (prefixWord ++ tailWord_741324) baseStart_741324 baseEnd_741324 := by
    simpa [prefixWord, tailWord_741324, baseEnd_741324] using wordTrace_append hprefix tailTrace_741324
  have hstable : (prefixWord ++ tailWord_741324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741324).length < 2 ^ (prefixWord ++ tailWord_741324).sum := by decide
  have hdescent : baseEnd_741324 < baseStart_741324 := by decide
  rcases family_descends (prefixWord ++ tailWord_741324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741351 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_741351 : Nat := 118140960795 + 741351 * 2 ^ 59
def prefixEnd_741351 : Nat := 4983230072969 + 3 ^ 40 * 741351 * 2
def baseEnd_741351 : Nat := 380669396691434194503095

theorem tailTrace_741351 : CollatzResearch.WordTrace tailWord_741351 prefixEnd_741351 380669396691434194503095 := by
  unfold tailWord_741351
  simp only [CollatzResearch.WordTrace]
  refine ⟨27039292337219414515759907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18026194891479609677173271 27039292337219414515759907)
  ·
    refine ⟨40558938505829121773639861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27039292337219414515759907 40558938505829121773639861)
    ·
      refine ⟨3802400484921480166278737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40558938505829121773639861 3802400484921480166278737)
      ·
        refine ⟨2851800363691110124709053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3802400484921480166278737 2851800363691110124709053)
        ·
          refine ⟨1069425136384166296765895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2851800363691110124709053 1069425136384166296765895)
          ·
            refine ⟨1604137704576249445148843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069425136384166296765895 1604137704576249445148843)
            ·
              refine ⟨2406206556864374167723265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604137704576249445148843 2406206556864374167723265)
              ·
                refine ⟨1804654917648280625792449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406206556864374167723265 1804654917648280625792449)
                ·
                  refine ⟨1353491188236210469344337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1804654917648280625792449 1353491188236210469344337)
                  ·
                    refine ⟨1015118391177157852008253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353491188236210469344337 1015118391177157852008253)
                    ·
                      refine ⟨380669396691434194503095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1015118391177157852008253 380669396691434194503095)
                      ·
                        rfl

theorem cell23_741351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_741351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741351 prefixEnd_741351 := by exact prefixLift 741351
  have htrace : WordTrace (prefixWord ++ tailWord_741351) baseStart_741351 baseEnd_741351 := by
    simpa [prefixWord, tailWord_741351, baseEnd_741351] using wordTrace_append hprefix tailTrace_741351
  have hstable : (prefixWord ++ tailWord_741351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741351).length < 2 ^ (prefixWord ++ tailWord_741351).sum := by decide
  have hdescent : baseEnd_741351 < baseStart_741351 := by decide
  rcases family_descends (prefixWord ++ tailWord_741351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741382 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_741382 : Nat := 118140960795 + 741382 * 2 ^ 59
def prefixEnd_741382 : Nat := 4983230072969 + 3 ^ 40 * 741382 * 2
def baseEnd_741382 : Nat := 380685314591723573215453

theorem tailTrace_741382 : CollatzResearch.WordTrace tailWord_741382 prefixEnd_741382 380685314591723573215453 := by
  unfold tailWord_741382
  simp only [CollatzResearch.WordTrace]
  refine ⟨845013218753347087816825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18026948666738071206758933 845013218753347087816825)
  ·
    refine ⟨633759914065010315862619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 845013218753347087816825 633759914065010315862619)
    ·
      refine ⟨950639871097515473793929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633759914065010315862619 950639871097515473793929)
      ·
        refine ⟨712979903323136605345447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 950639871097515473793929 712979903323136605345447)
        ·
          refine ⟨1069469854984704908018171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712979903323136605345447 1069469854984704908018171)
          ·
            refine ⟨1604204782477057362027257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069469854984704908018171 1604204782477057362027257)
            ·
              refine ⟨1203153586857793021520443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604204782477057362027257 1203153586857793021520443)
              ·
                refine ⟨1804730380286689532280665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203153586857793021520443 1804730380286689532280665)
                ·
                  refine ⟨1353547785215017149210499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1804730380286689532280665 1353547785215017149210499)
                  ·
                    refine ⟨2030321677822525723815749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1353547785215017149210499 2030321677822525723815749)
                    ·
                      refine ⟨380685314591723573215453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2030321677822525723815749 380685314591723573215453)
                      ·
                        rfl

theorem cell23_741382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_741382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741382 prefixEnd_741382 := by exact prefixLift 741382
  have htrace : WordTrace (prefixWord ++ tailWord_741382) baseStart_741382 baseEnd_741382 := by
    simpa [prefixWord, tailWord_741382, baseEnd_741382] using wordTrace_append hprefix tailTrace_741382
  have hstable : (prefixWord ++ tailWord_741382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741382).length < 2 ^ (prefixWord ++ tailWord_741382).sum := by decide
  have hdescent : baseEnd_741382 < baseStart_741382 := by decide
  rcases family_descends (prefixWord ++ tailWord_741382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741424 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 3]
def baseStart_741424 : Nat := 118140960795 + 741424 * 2 ^ 59
def prefixEnd_741424 : Nat := 4983230072969 + 3 ^ 40 * 741424 * 2
def baseEnd_741424 : Nat := 380706880779212408890259

theorem tailTrace_741424 : CollatzResearch.WordTrace tailWord_741424 prefixEnd_741424 380706880779212408890259 := by
  unfold tailWord_741424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13520977432977473991583663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18027969910636631988778217 13520977432977473991583663)
  ·
    refine ⟨20281466149466210987375495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13520977432977473991583663 20281466149466210987375495)
    ·
      refine ⟨30422199224199316481063243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20281466149466210987375495 30422199224199316481063243)
      ·
        refine ⟨45633298836298974721594865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30422199224199316481063243 45633298836298974721594865)
        ·
          refine ⟨34224974127224231041196149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45633298836298974721594865 34224974127224231041196149)
          ·
            refine ⟨3208591324427271660112139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34224974127224231041196149 3208591324427271660112139)
            ·
              refine ⟨4812886986640907490168209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208591324427271660112139 4812886986640907490168209)
              ·
                refine ⟨3609665239980680617626157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4812886986640907490168209 3609665239980680617626157)
                ·
                  refine ⟨1353624464992755231609809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3609665239980680617626157 1353624464992755231609809)
                  ·
                    refine ⟨1015218348744566423707357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353624464992755231609809 1015218348744566423707357)
                    ·
                      refine ⟨380706880779212408890259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1015218348744566423707357 380706880779212408890259)
                      ·
                        rfl

theorem cell23_741424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_741424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741424 prefixEnd_741424 := by exact prefixLift 741424
  have htrace : WordTrace (prefixWord ++ tailWord_741424) baseStart_741424 baseEnd_741424 := by
    simpa [prefixWord, tailWord_741424, baseEnd_741424] using wordTrace_append hprefix tailTrace_741424
  have hstable : (prefixWord ++ tailWord_741424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741424).length < 2 ^ (prefixWord ++ tailWord_741424).sum := by decide
  have hdescent : baseEnd_741424 < baseStart_741424 := by decide
  rcases family_descends (prefixWord ++ tailWord_741424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741427 : List Nat := [1, 1, 1, 2, 4, 1, 5, 8]
def baseStart_741427 : Nat := 118140960795 + 741427 * 2 ^ 59
def prefixEnd_741427 : Nat := 4983230072969 + 3 ^ 40 * 741427 * 2
def baseEnd_741427 : Nat := 14100311897080588783435

theorem tailTrace_741427 : CollatzResearch.WordTrace tailWord_741427 prefixEnd_741427 14100311897080588783435 := by
  unfold tailWord_741427
  simp only [CollatzResearch.WordTrace]
  refine ⟨27042064284944079495526535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18028042856629386330351023 27042064284944079495526535)
  ·
    refine ⟨40563096427416119243289803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27042064284944079495526535 40563096427416119243289803)
    ·
      refine ⟨60844644641124178864934705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40563096427416119243289803 60844644641124178864934705)
      ·
        refine ⟨45633483480843134148701029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60844644641124178864934705 45633483480843134148701029)
        ·
          refine ⟨8556278152658087652881443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45633483480843134148701029 8556278152658087652881443)
          ·
            refine ⟨12834417228987131479322165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8556278152658087652881443 12834417228987131479322165)
            ·
              refine ⟨1203226615217543576186453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12834417228987131479322165 1203226615217543576186453)
              ·
                refine ⟨14100311897080588783435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1203226615217543576186453 14100311897080588783435)
                ·
                  rfl

theorem cell23_741427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 8].length) (baseStart_741427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741427 prefixEnd_741427 := by exact prefixLift 741427
  have htrace : WordTrace (prefixWord ++ tailWord_741427) baseStart_741427 baseEnd_741427 := by
    simpa [prefixWord, tailWord_741427, baseEnd_741427] using wordTrace_append hprefix tailTrace_741427
  have hstable : (prefixWord ++ tailWord_741427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741427).length < 2 ^ (prefixWord ++ tailWord_741427).sum := by decide
  have hdescent : baseEnd_741427 < baseStart_741427 := by decide
  rcases family_descends (prefixWord ++ tailWord_741427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741441 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_741441 : Nat := 118140960795 + 741441 * 2 ^ 59
def prefixEnd_741441 : Nat := 4983230072969 + 3 ^ 40 * 741441 * 2
def baseEnd_741441 : Nat := 380715609950338842377681

theorem tailTrace_741441 : CollatzResearch.WordTrace tailWord_741441 prefixEnd_741441 380715609950338842377681 := by
  unfold tailWord_741441
  simp only [CollatzResearch.WordTrace]
  refine ⟨27042574906893359886536177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18028383271262239924357451 27042574906893359886536177)
  ·
    refine ⟨20281931180170019914902133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27042574906893359886536177 20281931180170019914902133)
    ·
      refine ⟨1901431048140939367022075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20281931180170019914902133 1901431048140939367022075)
      ·
        refine ⟨2852146572211409050533113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901431048140939367022075 2852146572211409050533113)
        ·
          refine ⟨2139109929158556787899835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852146572211409050533113 2139109929158556787899835)
          ·
            refine ⟨3208664893737835181849753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139109929158556787899835 3208664893737835181849753)
            ·
              refine ⟨2406498670303376386387315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3208664893737835181849753 2406498670303376386387315)
              ·
                refine ⟨3609748005455064579580973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406498670303376386387315 3609748005455064579580973)
                ·
                  refine ⟨1353655502045649217342865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3609748005455064579580973 1353655502045649217342865)
                  ·
                    refine ⟨1015241626534236913007149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353655502045649217342865 1015241626534236913007149)
                    ·
                      refine ⟨380715609950338842377681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1015241626534236913007149 380715609950338842377681)
                      ·
                        rfl

theorem cell23_741441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_741441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741441 prefixEnd_741441 := by exact prefixLift 741441
  have htrace : WordTrace (prefixWord ++ tailWord_741441) baseStart_741441 baseEnd_741441 := by
    simpa [prefixWord, tailWord_741441, baseEnd_741441] using wordTrace_append hprefix tailTrace_741441
  have hstable : (prefixWord ++ tailWord_741441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741441).length < 2 ^ (prefixWord ++ tailWord_741441).sum := by decide
  have hdescent : baseEnd_741441 < baseStart_741441 := by decide
  rcases family_descends (prefixWord ++ tailWord_741441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741458 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_741458 : Nat := 118140960795 + 741458 * 2 ^ 59
def prefixEnd_741458 : Nat := 4983230072969 + 3 ^ 40 * 741458 * 2
def baseEnd_741458 : Nat := 380724339121465275865103

theorem tailTrace_741458 : CollatzResearch.WordTrace tailWord_741458 prefixEnd_741458 380724339121465275865103 := by
  unfold tailWord_741458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760798736957942947476257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18028796631887847859936685 6760798736957942947476257)
  ·
    refine ⟨5070599052718457210607193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6760798736957942947476257 5070599052718457210607193)
    ·
      refine ⟨3802949289538842907955395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5070599052718457210607193 3802949289538842907955395)
      ·
        refine ⟨5704423934308264361933093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3802949289538842907955395 5704423934308264361933093)
        ·
          refine ⟨1069579487682799567862455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5704423934308264361933093 1069579487682799567862455)
          ·
            refine ⟨1604369231524199351793683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069579487682799567862455 1604369231524199351793683)
            ·
              refine ⟨2406553847286299027690525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604369231524199351793683 2406553847286299027690525)
              ·
                refine ⟨902457692732362135383947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2406553847286299027690525 902457692732362135383947)
                ·
                  refine ⟨1353686539098543203075921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902457692732362135383947 1353686539098543203075921)
                  ·
                    refine ⟨1015264904323907402306941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1353686539098543203075921 1015264904323907402306941)
                    ·
                      refine ⟨380724339121465275865103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1015264904323907402306941 380724339121465275865103)
                      ·
                        rfl

theorem cell23_741458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_741458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741458 prefixEnd_741458 := by exact prefixLift 741458
  have htrace : WordTrace (prefixWord ++ tailWord_741458) baseStart_741458 baseEnd_741458 := by
    simpa [prefixWord, tailWord_741458, baseEnd_741458] using wordTrace_append hprefix tailTrace_741458
  have hstable : (prefixWord ++ tailWord_741458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741458).length < 2 ^ (prefixWord ++ tailWord_741458).sum := by decide
  have hdescent : baseEnd_741458 < baseStart_741458 := by decide
  rcases family_descends (prefixWord ++ tailWord_741458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741471 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 3]
def baseStart_741471 : Nat := 118140960795 + 741471 * 2 ^ 59
def prefixEnd_741471 : Nat := 4983230072969 + 3 ^ 40 * 741471 * 2
def baseEnd_741471 : Nat := 380731014369973725002543

theorem tailTrace_741471 : CollatzResearch.WordTrace tailWord_741471 prefixEnd_741471 380731014369973725002543 := by
  unfold tailWord_741471
  simp only [CollatzResearch.WordTrace]
  refine ⟨27043669096784675010128267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18029112731189783340085511 27043669096784675010128267)
  ·
    refine ⟨40565503645177012515192401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27043669096784675010128267 40565503645177012515192401)
    ·
      refine ⟨30424127733882759386394301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40565503645177012515192401 30424127733882759386394301)
      ·
        refine ⟨11409047900206034769897863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30424127733882759386394301 11409047900206034769897863)
        ·
          refine ⟨17113571850309052154846795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11409047900206034769897863 17113571850309052154846795)
          ·
            refine ⟨25670357775463578232270193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17113571850309052154846795 25670357775463578232270193)
            ·
              refine ⟨19252768331597683674202645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25670357775463578232270193 19252768331597683674202645)
              ·
                refine ⟨902473515543641422228249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19252768331597683674202645 902473515543641422228249)
                ·
                  refine ⟨676855136657731066671187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 902473515543641422228249 676855136657731066671187)
                  ·
                    refine ⟨1015282704986596600006781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 676855136657731066671187 1015282704986596600006781)
                    ·
                      refine ⟨380731014369973725002543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1015282704986596600006781 380731014369973725002543)
                      ·
                        rfl

theorem cell23_741471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_741471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741471 prefixEnd_741471 := by exact prefixLift 741471
  have htrace : WordTrace (prefixWord ++ tailWord_741471) baseStart_741471 baseEnd_741471 := by
    simpa [prefixWord, tailWord_741471, baseEnd_741471] using wordTrace_append hprefix tailTrace_741471
  have hstable : (prefixWord ++ tailWord_741471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741471).length < 2 ^ (prefixWord ++ tailWord_741471).sum := by decide
  have hdescent : baseEnd_741471 < baseStart_741471 := by decide
  rcases family_descends (prefixWord ++ tailWord_741471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741511 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_741511 : Nat := 118140960795 + 741511 * 2 ^ 59
def prefixEnd_741511 : Nat := 4983230072969 + 3 ^ 40 * 741511 * 2
def baseEnd_741511 : Nat := 380751553596153568502359

theorem tailTrace_741511 : CollatzResearch.WordTrace tailWord_741511 prefixEnd_741511 380751553596153568502359 := by
  unfold tailWord_741511
  simp only [CollatzResearch.WordTrace]
  refine ⟨27045128016639761841584387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18030085344426507894389591 27045128016639761841584387)
  ·
    refine ⟨40567692024959642762376581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27045128016639761841584387 40567692024959642762376581)
    ·
      refine ⟨7606442254679933017945609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40567692024959642762376581 7606442254679933017945609)
      ·
        refine ⟨5704831691009949763459207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7606442254679933017945609 5704831691009949763459207)
        ·
          refine ⟨8557247536514924645188811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5704831691009949763459207 8557247536514924645188811)
          ·
            refine ⟨12835871304772386967783217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8557247536514924645188811 12835871304772386967783217)
            ·
              refine ⟨9626903478579290225837413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12835871304772386967783217 9626903478579290225837413)
              ·
                refine ⟨1805044402233616917344515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9626903478579290225837413 1805044402233616917344515)
                ·
                  refine ⟨2707566603350425376016773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805044402233616917344515 2707566603350425376016773)
                  ·
                    refine ⟨507668738128204758003145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2707566603350425376016773 507668738128204758003145)
                    ·
                      refine ⟨380751553596153568502359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507668738128204758003145 380751553596153568502359)
                      ·
                        rfl

theorem cell23_741511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_741511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741511 prefixEnd_741511 := by exact prefixLift 741511
  have htrace : WordTrace (prefixWord ++ tailWord_741511) baseStart_741511 baseEnd_741511 := by
    simpa [prefixWord, tailWord_741511, baseEnd_741511] using wordTrace_append hprefix tailTrace_741511
  have hstable : (prefixWord ++ tailWord_741511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741511).length < 2 ^ (prefixWord ++ tailWord_741511).sum := by decide
  have hdescent : baseEnd_741511 < baseStart_741511 := by decide
  rcases family_descends (prefixWord ++ tailWord_741511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741514 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_741514 : Nat := 118140960795 + 741514 * 2 ^ 59
def prefixEnd_741514 : Nat := 4983230072969 + 3 ^ 40 * 741514 * 2
def baseEnd_741514 : Nat := 380753094038117056764845

theorem tailTrace_741514 : CollatzResearch.WordTrace tailWord_741514 prefixEnd_741514 380753094038117056764845 := by
  unfold tailWord_741514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6761309358907223338485899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18030158290419262235962397 6761309358907223338485899)
  ·
    refine ⟨10141964038360835007728849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6761309358907223338485899 10141964038360835007728849)
    ·
      refine ⟨7606473028770626255796637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10141964038360835007728849 7606473028770626255796637)
      ·
        refine ⟨2852427385788984845923739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7606473028770626255796637 2852427385788984845923739)
        ·
          refine ⟨4278641078683477268885609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852427385788984845923739 4278641078683477268885609)
          ·
            refine ⟨3208980809012607951664207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278641078683477268885609 3208980809012607951664207)
            ·
              refine ⟨4813471213518911927496311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208980809012607951664207 4813471213518911927496311)
              ·
                refine ⟨7220206820278367891244467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813471213518911927496311 7220206820278367891244467)
                ·
                  refine ⟨10830310230417551836866701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7220206820278367891244467 10830310230417551836866701)
                  ·
                    refine ⟨4061366336406581938825013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10830310230417551836866701 4061366336406581938825013)
                    ·
                      refine ⟨380753094038117056764845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4061366336406581938825013 380753094038117056764845)
                      ·
                        rfl

theorem cell23_741514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_741514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741514 prefixEnd_741514 := by exact prefixLift 741514
  have htrace : WordTrace (prefixWord ++ tailWord_741514) baseStart_741514 baseEnd_741514 := by
    simpa [prefixWord, tailWord_741514, baseEnd_741514] using wordTrace_append hprefix tailTrace_741514
  have hstable : (prefixWord ++ tailWord_741514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741514).length < 2 ^ (prefixWord ++ tailWord_741514).sum := by decide
  have hdescent : baseEnd_741514 < baseStart_741514 := by decide
  rcases family_descends (prefixWord ++ tailWord_741514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741611 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 3, 4]
def baseStart_741611 : Nat := 118140960795 + 741611 * 2 ^ 59
def prefixEnd_741611 : Nat := 4983230072969 + 3 ^ 40 * 741611 * 2
def baseEnd_741611 : Nat := 126934300553867725750633

theorem tailTrace_741611 : CollatzResearch.WordTrace tailWord_741611 prefixEnd_741611 126934300553867725750633 := by
  unfold tailWord_741611
  simp only [CollatzResearch.WordTrace]
  refine ⟨27048775316277478920224687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18032516877518319280149791 27048775316277478920224687)
  ·
    refine ⟨40573162974416218380337031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27048775316277478920224687 40573162974416218380337031)
    ·
      refine ⟨60859744461624327570505547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40573162974416218380337031 60859744461624327570505547)
      ·
        refine ⟨91289616692436491355758321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60859744461624327570505547 91289616692436491355758321)
        ·
          refine ⟨68467212519327368516818741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91289616692436491355758321 68467212519327368516818741)
          ·
            refine ⟨6418801173686940798451757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68467212519327368516818741 6418801173686940798451757)
            ·
              refine ⟨2407050440132602799419409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6418801173686940798451757 2407050440132602799419409)
              ·
                refine ⟨1805287830099452099564557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407050440132602799419409 1805287830099452099564557)
                ·
                  refine ⟨676982936287294537336709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1805287830099452099564557 676982936287294537336709)
                  ·
                    refine ⟨126934300553867725750633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 676982936287294537336709 126934300553867725750633)
                    ·
                      rfl

theorem cell23_741611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 4].length) (baseStart_741611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741611 prefixEnd_741611 := by exact prefixLift 741611
  have htrace : WordTrace (prefixWord ++ tailWord_741611) baseStart_741611 baseEnd_741611 := by
    simpa [prefixWord, tailWord_741611, baseEnd_741611] using wordTrace_append hprefix tailTrace_741611
  have hstable : (prefixWord ++ tailWord_741611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741611).length < 2 ^ (prefixWord ++ tailWord_741611).sum := by decide
  have hdescent : baseEnd_741611 < baseStart_741611 := by decide
  rcases family_descends (prefixWord ++ tailWord_741611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741618 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_741618 : Nat := 118140960795 + 741618 * 2 ^ 59
def prefixEnd_741618 : Nat := 4983230072969 + 3 ^ 40 * 741618 * 2
def baseEnd_741618 : Nat := 380806496026184649864367

theorem tailTrace_741618 : CollatzResearch.WordTrace tailWord_741618 prefixEnd_741618 380806496026184649864367 := by
  unfold tailWord_741618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6762257656813029778932377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18032687084834746077153005 6762257656813029778932377)
  ·
    refine ⟨5071693242609772334199283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6762257656813029778932377 5071693242609772334199283)
    ·
      refine ⟨7607539863914658501298925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5071693242609772334199283 7607539863914658501298925)
      ·
        refine ⟨2852827448967996937987097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7607539863914658501298925 2852827448967996937987097)
        ·
          refine ⟨2139620586725997703490323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852827448967996937987097 2139620586725997703490323)
          ·
            refine ⟨3209430880088996555235485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139620586725997703490323 3209430880088996555235485)
            ·
              refine ⟨1203536580033373708213307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3209430880088996555235485 1203536580033373708213307)
              ·
                refine ⟨1805304870050060562319961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203536580033373708213307 1805304870050060562319961)
                ·
                  refine ⟨1353978652537545421739971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1805304870050060562319961 1353978652537545421739971)
                  ·
                    refine ⟨2030967978806318132609957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1353978652537545421739971 2030967978806318132609957)
                    ·
                      refine ⟨380806496026184649864367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2030967978806318132609957 380806496026184649864367)
                      ·
                        rfl

theorem cell23_741618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_741618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741618 prefixEnd_741618 := by exact prefixLift 741618
  have htrace : WordTrace (prefixWord ++ tailWord_741618) baseStart_741618 baseEnd_741618 := by
    simpa [prefixWord, tailWord_741618, baseEnd_741618] using wordTrace_append hprefix tailTrace_741618
  have hstable : (prefixWord ++ tailWord_741618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741618).length < 2 ^ (prefixWord ++ tailWord_741618).sum := by decide
  have hdescent : baseEnd_741618 < baseStart_741618 := by decide
  rcases family_descends (prefixWord ++ tailWord_741618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741641 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 6]
def baseStart_741641 : Nat := 118140960795 + 741641 * 2 ^ 59
def prefixEnd_741641 : Nat := 4983230072969 + 3 ^ 40 * 741641 * 2
def baseEnd_741641 : Nat := 42313145120137562208529

theorem tailTrace_741641 : CollatzResearch.WordTrace tailWord_741641 prefixEnd_741641 42313145120137562208529 := by
  unfold tailWord_741641
  simp only [CollatzResearch.WordTrace]
  refine ⟨27049869506168794043816777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18033246337445862695877851 27049869506168794043816777)
  ·
    refine ⟨20287402129626595532862583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27049869506168794043816777 20287402129626595532862583)
    ·
      refine ⟨30431103194439893299293875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20287402129626595532862583 30431103194439893299293875)
      ·
        refine ⟨45646654791659839948940813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30431103194439893299293875 45646654791659839948940813)
        ·
          refine ⟨17117495546872439980852805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45646654791659839948940813 17117495546872439980852805)
          ·
            refine ⟨3209530415038582496409901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17117495546872439980852805 3209530415038582496409901)
            ·
              refine ⟨1203573905639468436153713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3209530415038582496409901 1203573905639468436153713)
              ·
                refine ⟨902680429229601327115285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203573905639468436153713 902680429229601327115285)
                ·
                  refine ⟨42313145120137562208529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 902680429229601327115285 42313145120137562208529)
                  ·
                    rfl

theorem cell23_741641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 6].length) (baseStart_741641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741641 prefixEnd_741641 := by exact prefixLift 741641
  have htrace : WordTrace (prefixWord ++ tailWord_741641) baseStart_741641 baseEnd_741641 := by
    simpa [prefixWord, tailWord_741641, baseEnd_741641] using wordTrace_append hprefix tailTrace_741641
  have hstable : (prefixWord ++ tailWord_741641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741641).length < 2 ^ (prefixWord ++ tailWord_741641).sum := by decide
  have hdescent : baseEnd_741641 < baseStart_741641 := by decide
  rcases family_descends (prefixWord ++ tailWord_741641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741644 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_741644 : Nat := 118140960795 + 741644 * 2 ^ 59
def prefixEnd_741644 : Nat := 4983230072969 + 3 ^ 40 * 741644 * 2
def baseEnd_741644 : Nat := 380819846523201548139247

theorem tailTrace_741644 : CollatzResearch.WordTrace tailWord_741644 prefixEnd_741644 380819846523201548139247 := by
  unfold tailWord_741644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13524989462578962778087993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18033319283438617037450657 13524989462578962778087993)
  ·
    refine ⟨10143742096934222083565995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13524989462578962778087993 10143742096934222083565995)
    ·
      refine ⟨15215613145401333125348993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10143742096934222083565995 15215613145401333125348993)
      ·
        refine ⟨11411709859050999844011745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15215613145401333125348993 11411709859050999844011745)
        ·
          refine ⟨8558782394288249883008809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11411709859050999844011745 8558782394288249883008809)
          ·
            refine ⟨6419086795716187412256607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8558782394288249883008809 6419086795716187412256607)
            ·
              refine ⟨9628630193574281118384911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419086795716187412256607 9628630193574281118384911)
              ·
                refine ⟨14442945290361421677577367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9628630193574281118384911 14442945290361421677577367)
                ·
                  refine ⟨21664417935542132516366051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14442945290361421677577367 21664417935542132516366051)
                  ·
                    refine ⟨32496626903313198774549077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21664417935542132516366051 32496626903313198774549077)
                    ·
                      refine ⟨380819846523201548139247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 32496626903313198774549077 380819846523201548139247)
                      ·
                        rfl

theorem cell23_741644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_741644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741644 prefixEnd_741644 := by exact prefixLift 741644
  have htrace : WordTrace (prefixWord ++ tailWord_741644) baseStart_741644 baseEnd_741644 := by
    simpa [prefixWord, tailWord_741644, baseEnd_741644] using wordTrace_append hprefix tailTrace_741644
  have hstable : (prefixWord ++ tailWord_741644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741644).length < 2 ^ (prefixWord ++ tailWord_741644).sum := by decide
  have hdescent : baseEnd_741644 < baseStart_741644 := by decide
  rcases family_descends (prefixWord ++ tailWord_741644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741721 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_741721 : Nat := 118140960795 + 741721 * 2 ^ 59
def prefixEnd_741721 : Nat := 4983230072969 + 3 ^ 40 * 741721 * 2
def baseEnd_741721 : Nat := 380859384533597746876393

theorem tailTrace_741721 : CollatzResearch.WordTrace tailWord_741721 prefixEnd_741721 380859384533597746876393 := by
  unfold tailWord_741721
  simp only [CollatzResearch.WordTrace]
  refine ⟨27052787345878967706729017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18035191563919311804486011 27052787345878967706729017)
  ·
    refine ⟨20289590509409225780046763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27052787345878967706729017 20289590509409225780046763)
    ·
      refine ⟨30434385764113838670070145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20289590509409225780046763 30434385764113838670070145)
      ·
        refine ⟨22825789323085379002552609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30434385764113838670070145 22825789323085379002552609)
        ·
          refine ⟨17119341992314034251914457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22825789323085379002552609 17119341992314034251914457)
          ·
            refine ⟨12839506494235525688935843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17119341992314034251914457 12839506494235525688935843)
            ·
              refine ⟨19259259741353288533403765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12839506494235525688935843 19259259741353288533403765)
              ·
                refine ⟨1805555600751870800006603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19259259741353288533403765 1805555600751870800006603)
                ·
                  refine ⟨2708333401127806200009905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805555600751870800006603 2708333401127806200009905)
                  ·
                    refine ⟨2031250050845854650007429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2708333401127806200009905 2031250050845854650007429)
                    ·
                      refine ⟨380859384533597746876393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2031250050845854650007429 380859384533597746876393)
                      ·
                        rfl

theorem cell23_741721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_741721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741721 prefixEnd_741721 := by exact prefixLift 741721
  have htrace : WordTrace (prefixWord ++ tailWord_741721) baseStart_741721 baseEnd_741721 := by
    simpa [prefixWord, tailWord_741721, baseEnd_741721] using wordTrace_append hprefix tailTrace_741721
  have hstable : (prefixWord ++ tailWord_741721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741721).length < 2 ^ (prefixWord ++ tailWord_741721).sum := by decide
  have hdescent : baseEnd_741721 < baseStart_741721 := by decide
  rcases family_descends (prefixWord ++ tailWord_741721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741738 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_741738 : Nat := 118140960795 + 741738 * 2 ^ 59
def prefixEnd_741738 : Nat := 4983230072969 + 3 ^ 40 * 741738 * 2
def baseEnd_741738 : Nat := 380868113704724180363815

theorem tailTrace_741738 : CollatzResearch.WordTrace tailWord_741738 prefixEnd_741738 380868113704724180363815 := by
  unfold tailWord_741738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6763351846704344902524467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18035604924544919740065245 6763351846704344902524467)
  ·
    refine ⟨10145027770056517353786701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6763351846704344902524467 10145027770056517353786701)
    ·
      refine ⟨3804385413771194007670013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10145027770056517353786701 3804385413771194007670013)
      ·
        refine ⟨1426644530164197752876255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3804385413771194007670013 1426644530164197752876255)
        ·
          refine ⟨2139966795246296629314383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426644530164197752876255 2139966795246296629314383)
          ·
            refine ⟨3209950192869444943971575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139966795246296629314383 3209950192869444943971575)
            ·
              refine ⟨4814925289304167415957363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209950192869444943971575 4814925289304167415957363)
              ·
                refine ⟨7222387933956251123936045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4814925289304167415957363 7222387933956251123936045)
                ·
                  refine ⟨2708395475233594171476017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7222387933956251123936045 2708395475233594171476017)
                  ·
                    refine ⟨2031296606425195628607013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2708395475233594171476017 2031296606425195628607013)
                    ·
                      refine ⟨380868113704724180363815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2031296606425195628607013 380868113704724180363815)
                      ·
                        rfl

theorem cell23_741738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_741738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741738 prefixEnd_741738 := by exact prefixLift 741738
  have htrace : WordTrace (prefixWord ++ tailWord_741738) baseStart_741738 baseEnd_741738 := by
    simpa [prefixWord, tailWord_741738, baseEnd_741738] using wordTrace_append hprefix tailTrace_741738
  have hstable : (prefixWord ++ tailWord_741738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741738).length < 2 ^ (prefixWord ++ tailWord_741738).sum := by decide
  have hdescent : baseEnd_741738 < baseStart_741738 := by decide
  rcases family_descends (prefixWord ++ tailWord_741738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741781 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_741781 : Nat := 118140960795 + 741781 * 2 ^ 59
def prefixEnd_741781 : Nat := 4983230072969 + 3 ^ 40 * 741781 * 2
def baseEnd_741781 : Nat := 380890193372867512126117

theorem tailTrace_741781 : CollatzResearch.WordTrace tailWord_741781 prefixEnd_741781 380890193372867512126117 := by
  unfold tailWord_741781
  simp only [CollatzResearch.WordTrace]
  refine ⟨27054975725661597953913197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18036650483774398635942131 27054975725661597953913197)
  ·
    refine ⟨10145615897123099232717449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27054975725661597953913197 10145615897123099232717449)
    ·
      refine ⟨7609211922842324424538087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10145615897123099232717449 7609211922842324424538087)
      ·
        refine ⟨11413817884263486636807131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609211922842324424538087 11413817884263486636807131)
        ·
          refine ⟨17120726826395229955210697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11413817884263486636807131 17120726826395229955210697)
          ·
            refine ⟨12840545119796422466408023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17120726826395229955210697 12840545119796422466408023)
            ·
              refine ⟨19260817679694633699612035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12840545119796422466408023 19260817679694633699612035)
              ·
                refine ⟨28891226519541950549418053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19260817679694633699612035 28891226519541950549418053)
                ·
                  refine ⟨5417104972414115728015885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28891226519541950549418053 5417104972414115728015885)
                  ·
                    refine ⟨2031414364655293398005957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5417104972414115728015885 2031414364655293398005957)
                    ·
                      refine ⟨380890193372867512126117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2031414364655293398005957 380890193372867512126117)
                      ·
                        rfl

theorem cell23_741781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_741781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741781 prefixEnd_741781 := by exact prefixLift 741781
  have htrace : WordTrace (prefixWord ++ tailWord_741781) baseStart_741781 baseEnd_741781 := by
    simpa [prefixWord, tailWord_741781, baseEnd_741781] using wordTrace_append hprefix tailTrace_741781
  have hstable : (prefixWord ++ tailWord_741781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741781).length < 2 ^ (prefixWord ++ tailWord_741781).sum := by decide
  have hdescent : baseEnd_741781 < baseStart_741781 := by decide
  rcases family_descends (prefixWord ++ tailWord_741781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741785 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 1, 3, 2]
def baseStart_741785 : Nat := 118140960795 + 741785 * 2 ^ 59
def prefixEnd_741785 : Nat := 4983230072969 + 3 ^ 40 * 741785 * 2
def baseEnd_741785 : Nat := 380892247295485496476099

theorem tailTrace_741785 : CollatzResearch.WordTrace tailWord_741785 prefixEnd_741785 380892247295485496476099 := by
  unfold tailWord_741785
  simp only [CollatzResearch.WordTrace]
  refine ⟨27055121617647106637058809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18036747745098071091372539 27055121617647106637058809)
  ·
    refine ⟨20291341213235329977794107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27055121617647106637058809 20291341213235329977794107)
    ·
      refine ⟨30437011819852994966691161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20291341213235329977794107 30437011819852994966691161)
      ·
        refine ⟨22827758864889746225018371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30437011819852994966691161 22827758864889746225018371)
        ·
          refine ⟨34241638297334619337527557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22827758864889746225018371 34241638297334619337527557)
          ·
            refine ⟨6420307180750241125786417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34241638297334619337527557 6420307180750241125786417)
            ·
              refine ⟨4815230385562680844339813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6420307180750241125786417 4815230385562680844339813)
              ·
                refine ⟨902855697293002658313715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4815230385562680844339813 902855697293002658313715)
                ·
                  refine ⟨1354283545939503987470573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902855697293002658313715 1354283545939503987470573)
                  ·
                    refine ⟨507856329727313995301465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354283545939503987470573 507856329727313995301465)
                    ·
                      refine ⟨380892247295485496476099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507856329727313995301465 380892247295485496476099)
                      ·
                        rfl

theorem cell23_741785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_741785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741785 prefixEnd_741785 := by exact prefixLift 741785
  have htrace : WordTrace (prefixWord ++ tailWord_741785) baseStart_741785 baseEnd_741785 := by
    simpa [prefixWord, tailWord_741785, baseEnd_741785] using wordTrace_append hprefix tailTrace_741785
  have hstable : (prefixWord ++ tailWord_741785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741785).length < 2 ^ (prefixWord ++ tailWord_741785).sum := by decide
  have hdescent : baseEnd_741785 < baseStart_741785 := by decide
  rcases family_descends (prefixWord ++ tailWord_741785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741791 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 1, 8]
def baseStart_741791 : Nat := 118140960795 + 741791 * 2 ^ 59
def prefixEnd_741791 : Nat := 4983230072969 + 3 ^ 40 * 741791 * 2
def baseEnd_741791 : Nat := 126965109393137491000357

theorem tailTrace_741791 : CollatzResearch.WordTrace tailWord_741791 prefixEnd_741791 126965109393137491000357 := by
  unfold tailWord_741791
  simp only [CollatzResearch.WordTrace]
  refine ⟨27055340455625369661777227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18036893637083579774518151 27055340455625369661777227)
  ·
    refine ⟨40583010683438054492665841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27055340455625369661777227 40583010683438054492665841)
    ·
      refine ⟨30437258012578540869499381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40583010683438054492665841 30437258012578540869499381)
      ·
        refine ⟨2853492938679238206515567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30437258012578540869499381 2853492938679238206515567)
        ·
          refine ⟨4280239408018857309773351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853492938679238206515567 4280239408018857309773351)
          ·
            refine ⟨6420359112028285964660027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280239408018857309773351 6420359112028285964660027)
            ·
              refine ⟨9630538668042428946990041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6420359112028285964660027 9630538668042428946990041)
              ·
                refine ⟨7222904001031821710242531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9630538668042428946990041 7222904001031821710242531)
                ·
                  refine ⟨10834356001547732565363797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7222904001031821710242531 10834356001547732565363797)
                  ·
                    refine ⟨126965109393137491000357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10834356001547732565363797 126965109393137491000357)
                    ·
                      rfl

theorem cell23_741791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_741791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741791 prefixEnd_741791 := by exact prefixLift 741791
  have htrace : WordTrace (prefixWord ++ tailWord_741791) baseStart_741791 baseEnd_741791 := by
    simpa [prefixWord, tailWord_741791, baseEnd_741791] using wordTrace_append hprefix tailTrace_741791
  have hstable : (prefixWord ++ tailWord_741791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741791).length < 2 ^ (prefixWord ++ tailWord_741791).sum := by decide
  have hdescent : baseEnd_741791 < baseStart_741791 := by decide
  rcases family_descends (prefixWord ++ tailWord_741791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741801 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_741801 : Nat := 118140960795 + 741801 * 2 ^ 59
def prefixEnd_741801 : Nat := 4983230072969 + 3 ^ 40 * 741801 * 2
def baseEnd_741801 : Nat := 380900462985957433876025

theorem tailTrace_741801 : CollatzResearch.WordTrace tailWord_741801 prefixEnd_741801 380900462985957433876025 := by
  unfold tailWord_741801
  simp only [CollatzResearch.WordTrace]
  refine ⟨27055705185589141369641257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18037136790392760913094171 27055705185589141369641257)
  ·
    refine ⟨20291778889191856027230943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27055705185589141369641257 20291778889191856027230943)
    ·
      refine ⟨30437668333787784040846415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20291778889191856027230943 30437668333787784040846415)
      ·
        refine ⟨45656502500681676061269623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30437668333787784040846415 45656502500681676061269623)
        ·
          refine ⟨68484753751022514091904435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45656502500681676061269623 68484753751022514091904435)
          ·
            refine ⟨102727130626533771137856653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68484753751022514091904435 102727130626533771137856653)
            ·
              refine ⟨38522673984950164176696245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102727130626533771137856653 38522673984950164176696245)
              ·
                refine ⟨3611500686089077891565273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38522673984950164176696245 3611500686089077891565273)
                ·
                  refine ⟨2708625514566808418673955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3611500686089077891565273 2708625514566808418673955)
                  ·
                    refine ⟨4062938271850212628010933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2708625514566808418673955 4062938271850212628010933)
                    ·
                      refine ⟨380900462985957433876025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4062938271850212628010933 380900462985957433876025)
                      ·
                        rfl

theorem cell23_741801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_741801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741801 prefixEnd_741801 := by exact prefixLift 741801
  have htrace : WordTrace (prefixWord ++ tailWord_741801) baseStart_741801 baseEnd_741801 := by
    simpa [prefixWord, tailWord_741801, baseEnd_741801] using wordTrace_append hprefix tailTrace_741801
  have hstable : (prefixWord ++ tailWord_741801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741801).length < 2 ^ (prefixWord ++ tailWord_741801).sum := by decide
  have hdescent : baseEnd_741801 < baseStart_741801 := by decide
  rcases family_descends (prefixWord ++ tailWord_741801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741832 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_741832 : Nat := 118140960795 + 741832 * 2 ^ 59
def prefixEnd_741832 : Nat := 4983230072969 + 3 ^ 40 * 741832 * 2
def baseEnd_741832 : Nat := 380916380886246812588383

theorem tailTrace_741832 : CollatzResearch.WordTrace tailWord_741832 prefixEnd_741832 380916380886246812588383 := by
  unfold tailWord_741832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13528417924238416832009875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18037890565651222442679833 13528417924238416832009875)
  ·
    refine ⟨20292626886357625248014813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13528417924238416832009875 20292626886357625248014813)
    ·
      refine ⟨7609735082384109468005555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20292626886357625248014813 7609735082384109468005555)
      ·
        refine ⟨11414602623576164202008333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609735082384109468005555 11414602623576164202008333)
        ·
          refine ⟨4280475983841061575753125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11414602623576164202008333 4280475983841061575753125)
          ·
            refine ⟨802589246970199045453711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4280475983841061575753125 802589246970199045453711)
            ·
              refine ⟨1203883870455298568180567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802589246970199045453711 1203883870455298568180567)
              ·
                refine ⟨1805825805682947852270851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203883870455298568180567 1805825805682947852270851)
                ·
                  refine ⟨2708738708524421778406277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805825805682947852270851 2708738708524421778406277)
                  ·
                    refine ⟨507888507848329083451177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2708738708524421778406277 507888507848329083451177)
                    ·
                      refine ⟨380916380886246812588383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 507888507848329083451177 380916380886246812588383)
                      ·
                        rfl

theorem cell23_741832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_741832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741832 prefixEnd_741832 := by exact prefixLift 741832
  have htrace : WordTrace (prefixWord ++ tailWord_741832) baseStart_741832 baseEnd_741832 := by
    simpa [prefixWord, tailWord_741832, baseEnd_741832] using wordTrace_append hprefix tailTrace_741832
  have hstable : (prefixWord ++ tailWord_741832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741832).length < 2 ^ (prefixWord ++ tailWord_741832).sum := by decide
  have hdescent : baseEnd_741832 < baseStart_741832 := by decide
  rcases family_descends (prefixWord ++ tailWord_741832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741855 : List Nat := [1, 1, 2, 3, 3, 2, 3, 3, 5]
def baseStart_741855 : Nat := 118140960795 + 741855 * 2 ^ 59
def prefixEnd_741855 : Nat := 4983230072969 + 3 ^ 40 * 741855 * 2
def baseEnd_741855 : Nat := 42325354549033358066753

theorem tailTrace_741855 : CollatzResearch.WordTrace tailWord_741855 prefixEnd_741855 42325354549033358066753 := by
  unfold tailWord_741855
  simp only [CollatzResearch.WordTrace]
  refine ⟨27057674727393508592107019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18038449818262339061404679 27057674727393508592107019)
  ·
    refine ⟨40586512091090262888160529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27057674727393508592107019 40586512091090262888160529)
    ·
      refine ⟨30439884068317697166120397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40586512091090262888160529 30439884068317697166120397)
      ·
        refine ⟨11414956525619136437295149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30439884068317697166120397 11414956525619136437295149)
        ·
          refine ⟨4280608697107176163985681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11414956525619136437295149 4280608697107176163985681)
          ·
            refine ⟨3210456522830382122989261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4280608697107176163985681 3210456522830382122989261)
            ·
              refine ⟨1203921196061393296120973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3210456522830382122989261 1203921196061393296120973)
              ·
                refine ⟨451470448523022486045365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1203921196061393296120973 451470448523022486045365)
                ·
                  refine ⟨42325354549033358066753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 451470448523022486045365 42325354549033358066753)
                  ·
                    rfl

theorem cell23_741855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 5].length) (baseStart_741855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741855 prefixEnd_741855 := by exact prefixLift 741855
  have htrace : WordTrace (prefixWord ++ tailWord_741855) baseStart_741855 baseEnd_741855 := by
    simpa [prefixWord, tailWord_741855, baseEnd_741855] using wordTrace_append hprefix tailTrace_741855
  have hstable : (prefixWord ++ tailWord_741855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741855).length < 2 ^ (prefixWord ++ tailWord_741855).sum := by decide
  have hdescent : baseEnd_741855 < baseStart_741855 := by decide
  rcases family_descends (prefixWord ++ tailWord_741855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741868 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_741868 : Nat := 118140960795 + 741868 * 2 ^ 59
def prefixEnd_741868 : Nat := 4983230072969 + 3 ^ 40 * 741868 * 2
def baseEnd_741868 : Nat := 126978288729936223912739

theorem tailTrace_741868 : CollatzResearch.WordTrace tailWord_741868 prefixEnd_741868 126978288729936223912739 := by
  unfold tailWord_741868
  simp only [CollatzResearch.WordTrace]
  refine ⟨13529074438173205906165129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18038765917564274541553505 13529074438173205906165129)
  ·
    refine ⟨10146805828629904429623847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13529074438173205906165129 10146805828629904429623847)
    ·
      refine ⟨15220208742944856644435771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10146805828629904429623847 15220208742944856644435771)
      ·
        refine ⟨22830313114417284966653657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15220208742944856644435771 22830313114417284966653657)
        ·
          refine ⟨17122734835812963724990243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22830313114417284966653657 17122734835812963724990243)
          ·
            refine ⟨25684102253719445587485365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17122734835812963724990243 25684102253719445587485365)
            ·
              refine ⟨2407884586286198023826753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25684102253719445587485365 2407884586286198023826753)
              ·
                refine ⟨1805913439714648517870065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407884586286198023826753 1805913439714648517870065)
                ·
                  refine ⟨1354435079785986388402549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1805913439714648517870065 1354435079785986388402549)
                  ·
                    refine ⟨126978288729936223912739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1354435079785986388402549 126978288729936223912739)
                    ·
                      rfl

theorem cell23_741868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_741868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741868 prefixEnd_741868 := by exact prefixLift 741868
  have htrace : WordTrace (prefixWord ++ tailWord_741868) baseStart_741868 baseEnd_741868 := by
    simpa [prefixWord, tailWord_741868, baseEnd_741868] using wordTrace_append hprefix tailTrace_741868
  have hstable : (prefixWord ++ tailWord_741868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741868).length < 2 ^ (prefixWord ++ tailWord_741868).sum := by decide
  have hdescent : baseEnd_741868 < baseStart_741868 := by decide
  rcases family_descends (prefixWord ++ tailWord_741868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741925 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_741925 : Nat := 118140960795 + 741925 * 2 ^ 59
def prefixEnd_741925 : Nat := 4983230072969 + 3 ^ 40 * 741925 * 2
def baseEnd_741925 : Nat := 380964134587114948725455

theorem tailTrace_741925 : CollatzResearch.WordTrace tailWord_741925 prefixEnd_741925 380964134587114948725455 := by
  unfold tailWord_741925
  simp only [CollatzResearch.WordTrace]
  refine ⟨27060227837139910547155229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18040151891426607031436819 27060227837139910547155229)
  ·
    refine ⟨10147585438927466455183211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27060227837139910547155229 10147585438927466455183211)
    ·
      refine ⟨15221378158391199682774817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10147585438927466455183211 15221378158391199682774817)
      ·
        refine ⟨11416033618793399762081113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15221378158391199682774817 11416033618793399762081113)
        ·
          refine ⟨8562025214095049821560835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11416033618793399762081113 8562025214095049821560835)
          ·
            refine ⟨12843037821142574732341253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8562025214095049821560835 12843037821142574732341253)
            ·
              refine ⟨2408069591464232762313985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12843037821142574732341253 2408069591464232762313985)
              ·
                refine ⟨1806052193598174571735489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2408069591464232762313985 1806052193598174571735489)
                ·
                  refine ⟨1354539145198630928801617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1806052193598174571735489 1354539145198630928801617)
                  ·
                    refine ⟨1015904358898973196601213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1354539145198630928801617 1015904358898973196601213)
                    ·
                      refine ⟨380964134587114948725455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1015904358898973196601213 380964134587114948725455)
                      ·
                        rfl

theorem cell23_741925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_741925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741925 prefixEnd_741925 := by exact prefixLift 741925
  have htrace : WordTrace (prefixWord ++ tailWord_741925) baseStart_741925 baseEnd_741925 := by
    simpa [prefixWord, tailWord_741925, baseEnd_741925] using wordTrace_append hprefix tailTrace_741925
  have hstable : (prefixWord ++ tailWord_741925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741925).length < 2 ^ (prefixWord ++ tailWord_741925).sum := by decide
  have hdescent : baseEnd_741925 < baseStart_741925 := by decide
  rcases family_descends (prefixWord ++ tailWord_741925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741975 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 1, 5]
def baseStart_741975 : Nat := 118140960795 + 741975 * 2 ^ 59
def prefixEnd_741975 : Nat := 4983230072969 + 3 ^ 40 * 741975 * 2
def baseEnd_741975 : Nat := 126996602873279917700075

theorem tailTrace_741975 : CollatzResearch.WordTrace tailWord_741975 prefixEnd_741975 126996602873279917700075 := by
  unfold tailWord_741975
  simp only [CollatzResearch.WordTrace]
  refine ⟨27062051486958769086475379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18041367657972512724316919 27062051486958769086475379)
  ·
    refine ⟨40593077230438153629713069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27062051486958769086475379 40593077230438153629713069)
    ·
      refine ⟨15222403961414307611142401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40593077230438153629713069 15222403961414307611142401)
      ·
        refine ⟨11416802971060730708356801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15222403961414307611142401 11416802971060730708356801)
        ·
          refine ⟨8562602228295548031267601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11416802971060730708356801 8562602228295548031267601)
          ·
            refine ⟨6421951671221661023450701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8562602228295548031267601 6421951671221661023450701)
            ·
              refine ⟨2408231876708122883794013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6421951671221661023450701 2408231876708122883794013)
              ·
                refine ⟨903086953765546081422755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2408231876708122883794013 903086953765546081422755)
                ·
                  refine ⟨1354630430648319122134133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903086953765546081422755 1354630430648319122134133)
                  ·
                    refine ⟨126996602873279917700075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1354630430648319122134133 126996602873279917700075)
                    ·
                      rfl

theorem cell23_741975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_741975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741975 prefixEnd_741975 := by exact prefixLift 741975
  have htrace : WordTrace (prefixWord ++ tailWord_741975) baseStart_741975 baseEnd_741975 := by
    simpa [prefixWord, tailWord_741975, baseEnd_741975] using wordTrace_append hprefix tailTrace_741975
  have hstable : (prefixWord ++ tailWord_741975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741975).length < 2 ^ (prefixWord ++ tailWord_741975).sum := by decide
  have hdescent : baseEnd_741975 < baseStart_741975 := by decide
  rcases family_descends (prefixWord ++ tailWord_741975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741989 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_741989 : Nat := 118140960795 + 741989 * 2 ^ 59
def prefixEnd_741989 : Nat := 4983230072969 + 3 ^ 40 * 741989 * 2
def baseEnd_741989 : Nat := 380996997349002698325161

theorem tailTrace_741989 : CollatzResearch.WordTrace tailWord_741989 prefixEnd_741989 380996997349002698325161 := by
  unfold tailWord_741989
  simp only [CollatzResearch.WordTrace]
  refine ⟨27062562108908049477485021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18041708072605366318323347 27062562108908049477485021)
  ·
    refine ⟨10148460790840518554056883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27062562108908049477485021 10148460790840518554056883)
    ·
      refine ⟨15222691186260777831085325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10148460790840518554056883 15222691186260777831085325)
      ·
        refine ⟨5708509194847791686656997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15222691186260777831085325 5708509194847791686656997)
        ·
          refine ⟨1070345474033960941248187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5708509194847791686656997 1070345474033960941248187)
          ·
            refine ⟨1605518211050941411872281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070345474033960941248187 1605518211050941411872281)
            ·
              refine ⟨1204138658288206058904211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605518211050941411872281 1204138658288206058904211)
              ·
                refine ⟨1806207987432309088356317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204138658288206058904211 1806207987432309088356317)
                ·
                  refine ⟨677327995287115908133619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1806207987432309088356317 677327995287115908133619)
                  ·
                    refine ⟨1015991992930673862200429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 677327995287115908133619 1015991992930673862200429)
                    ·
                      refine ⟨380996997349002698325161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1015991992930673862200429 380996997349002698325161)
                      ·
                        rfl

theorem cell23_741989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_741989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_741989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_741989 prefixEnd_741989 := by exact prefixLift 741989
  have htrace : WordTrace (prefixWord ++ tailWord_741989) baseStart_741989 baseEnd_741989 := by
    simpa [prefixWord, tailWord_741989, baseEnd_741989] using wordTrace_append hprefix tailTrace_741989
  have hstable : (prefixWord ++ tailWord_741989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741989).length < 2 ^ (prefixWord ++ tailWord_741989).sum := by decide
  have hdescent : baseEnd_741989 < baseStart_741989 := by decide
  rcases family_descends (prefixWord ++ tailWord_741989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742008 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_742008 : Nat := 118140960795 + 742008 * 2 ^ 59
def prefixEnd_742008 : Nat := 4983230072969 + 3 ^ 40 * 742008 * 2
def baseEnd_742008 : Nat := 381006753481438123987573

theorem tailTrace_742008 : CollatzResearch.WordTrace tailWord_742008 prefixEnd_742008 381006753481438123987573 := by
  unfold tailWord_742008
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531627547919607861213339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18042170063892810481617785 13531627547919607861213339)
  ·
    refine ⟨20297441321879411791820009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13531627547919607861213339 20297441321879411791820009)
    ·
      refine ⟨15223080991409558843865007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20297441321879411791820009 15223080991409558843865007)
      ·
        refine ⟨22834621487114338265797511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15223080991409558843865007 22834621487114338265797511)
        ·
          refine ⟨34251932230671507398696267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22834621487114338265797511 34251932230671507398696267)
          ·
            refine ⟨51377898346007261098044401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34251932230671507398696267 51377898346007261098044401)
            ·
              refine ⟨38533423759505445823533301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51377898346007261098044401 38533423759505445823533301)
              ·
                refine ⟨3612508477453635545956247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38533423759505445823533301 3612508477453635545956247)
                ·
                  refine ⟨5418762716180453318934371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612508477453635545956247 5418762716180453318934371)
                  ·
                    refine ⟨8128144074270679978401557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5418762716180453318934371 8128144074270679978401557)
                    ·
                      refine ⟨381006753481438123987573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8128144074270679978401557 381006753481438123987573)
                      ·
                        rfl

theorem cell23_742008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_742008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742008 prefixEnd_742008 := by exact prefixLift 742008
  have htrace : WordTrace (prefixWord ++ tailWord_742008) baseStart_742008 baseEnd_742008 := by
    simpa [prefixWord, tailWord_742008, baseEnd_742008] using wordTrace_append hprefix tailTrace_742008
  have hstable : (prefixWord ++ tailWord_742008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742008).length < 2 ^ (prefixWord ++ tailWord_742008).sum := by decide
  have hdescent : baseEnd_742008 < baseStart_742008 := by decide
  rcases family_descends (prefixWord ++ tailWord_742008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742105 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 3]
def baseStart_742105 : Nat := 118140960795 + 742105 * 2 ^ 59
def prefixEnd_742105 : Nat := 4983230072969 + 3 ^ 40 * 742105 * 2
def baseEnd_742105 : Nat := 381056561104924244474627

theorem tailTrace_742105 : CollatzResearch.WordTrace tailWord_742105 prefixEnd_742105 381056561104924244474627 := by
  unfold tailWord_742105
  simp only [CollatzResearch.WordTrace]
  refine ⟨27066792976487801288707769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18044528650991867525805179 27066792976487801288707769)
  ·
    refine ⟨20300094732365850966530827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27066792976487801288707769 20300094732365850966530827)
    ·
      refine ⟨30450142098548776449796241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20300094732365850966530827 30450142098548776449796241)
      ·
        refine ⟨22837606573911582337347181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30450142098548776449796241 22837606573911582337347181)
        ·
          refine ⟨8564102465216843376505193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22837606573911582337347181 8564102465216843376505193)
          ·
            refine ⟨6423076848912632532378895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8564102465216843376505193 6423076848912632532378895)
            ·
              refine ⟨9634615273368948798568343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6423076848912632532378895 9634615273368948798568343)
              ·
                refine ⟨14451922910053423197852515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634615273368948798568343 14451922910053423197852515)
                ·
                  refine ⟨21677884365080134796778773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14451922910053423197852515 21677884365080134796778773)
                  ·
                    refine ⟨1016150829613131318599005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21677884365080134796778773 1016150829613131318599005)
                    ·
                      refine ⟨381056561104924244474627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1016150829613131318599005 381056561104924244474627)
                      ·
                        rfl

theorem cell23_742105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_742105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742105 prefixEnd_742105 := by exact prefixLift 742105
  have htrace : WordTrace (prefixWord ++ tailWord_742105) baseStart_742105 baseEnd_742105 := by
    simpa [prefixWord, tailWord_742105, baseEnd_742105] using wordTrace_append hprefix tailTrace_742105
  have hstable : (prefixWord ++ tailWord_742105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742105).length < 2 ^ (prefixWord ++ tailWord_742105).sum := by decide
  have hdescent : baseEnd_742105 < baseStart_742105 := by decide
  rcases family_descends (prefixWord ++ tailWord_742105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742135 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_742135 : Nat := 118140960795 + 742135 * 2 ^ 59
def prefixEnd_742135 : Nat := 4983230072969 + 3 ^ 40 * 742135 * 2
def baseEnd_742135 : Nat := 381071965524559127099489

theorem tailTrace_742135 : CollatzResearch.WordTrace tailWord_742135 prefixEnd_742135 381071965524559127099489 := by
  unfold tailWord_742135
  simp only [CollatzResearch.WordTrace]
  refine ⟨27067887166379116412299859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18045258110919410941533239 27067887166379116412299859)
  ·
    refine ⟨40601830749568674618449789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27067887166379116412299859 40601830749568674618449789)
    ·
      refine ⟨15225686531088252981918671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40601830749568674618449789 15225686531088252981918671)
      ·
        refine ⟨22838529796632379472878007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15225686531088252981918671 22838529796632379472878007)
        ·
          refine ⟨34257794694948569209317011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22838529796632379472878007 34257794694948569209317011)
          ·
            refine ⟨51386692042422853813975517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34257794694948569209317011 51386692042422853813975517)
            ·
              refine ⟨19270009515908570180240819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51386692042422853813975517 19270009515908570180240819)
              ·
                refine ⟨28905014273862855270361229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19270009515908570180240819 28905014273862855270361229)
                ·
                  refine ⟨10839380352698570726385461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28905014273862855270361229 10839380352698570726385461)
                  ·
                    refine ⟨1016191908065491005598637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10839380352698570726385461 1016191908065491005598637)
                    ·
                      refine ⟨381071965524559127099489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1016191908065491005598637 381071965524559127099489)
                      ·
                        rfl

theorem cell23_742135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_742135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742135 prefixEnd_742135 := by exact prefixLift 742135
  have htrace : WordTrace (prefixWord ++ tailWord_742135) baseStart_742135 baseEnd_742135 := by
    simpa [prefixWord, tailWord_742135, baseEnd_742135] using wordTrace_append hprefix tailTrace_742135
  have hstable : (prefixWord ++ tailWord_742135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742135).length < 2 ^ (prefixWord ++ tailWord_742135).sum := by decide
  have hdescent : baseEnd_742135 < baseStart_742135 := by decide
  rcases family_descends (prefixWord ++ tailWord_742135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742152 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_742152 : Nat := 118140960795 + 742152 * 2 ^ 59
def prefixEnd_742152 : Nat := 4983230072969 + 3 ^ 40 * 742152 * 2
def baseEnd_742152 : Nat := 381080694695685560586911

theorem tailTrace_742152 : CollatzResearch.WordTrace tailWord_742152 prefixEnd_742152 381080694695685560586911 := by
  unfold tailWord_742152
  simp only [CollatzResearch.WordTrace]
  refine ⟨13534253603658764157834355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18045671471545018877112473 13534253603658764157834355)
  ·
    refine ⟨20301380405488146236751533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13534253603658764157834355 20301380405488146236751533)
    ·
      refine ⟨7613017652058054838781825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20301380405488146236751533 7613017652058054838781825)
      ·
        refine ⟨5709763239043541129086369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7613017652058054838781825 5709763239043541129086369)
        ·
          refine ⟨4282322429282655846814777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5709763239043541129086369 4282322429282655846814777)
          ·
            refine ⟨3211741821961991885111083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4282322429282655846814777 3211741821961991885111083)
            ·
              refine ⟨4817612732942987827666625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211741821961991885111083 4817612732942987827666625)
              ·
                refine ⟨3613209549707240870749969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4817612732942987827666625 3613209549707240870749969)
                ·
                  refine ⟨2709907162280430653062477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3613209549707240870749969 2709907162280430653062477)
                  ·
                    refine ⟨1016215185855161494898429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2709907162280430653062477 1016215185855161494898429)
                    ·
                      refine ⟨381080694695685560586911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1016215185855161494898429 381080694695685560586911)
                      ·
                        rfl

theorem cell23_742152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_742152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742152 prefixEnd_742152 := by exact prefixLift 742152
  have htrace : WordTrace (prefixWord ++ tailWord_742152) baseStart_742152 baseEnd_742152 := by
    simpa [prefixWord, tailWord_742152, baseEnd_742152] using wordTrace_append hprefix tailTrace_742152
  have hstable : (prefixWord ++ tailWord_742152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742152).length < 2 ^ (prefixWord ++ tailWord_742152).sum := by decide
  have hdescent : baseEnd_742152 < baseStart_742152 := by decide
  rcases family_descends (prefixWord ++ tailWord_742152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742155 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 4, 5]
def baseStart_742155 : Nat := 118140960795 + 742155 * 2 ^ 59
def prefixEnd_742155 : Nat := 4983230072969 + 3 ^ 40 * 742155 * 2
def baseEnd_742155 : Nat := 127027411712549682949799

theorem tailTrace_742155 : CollatzResearch.WordTrace tailWord_742155 prefixEnd_742155 127027411712549682949799 := by
  unfold tailWord_742155
  simp only [CollatzResearch.WordTrace]
  refine ⟨27068616626306659828027919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18045744417537773218685279 27068616626306659828027919)
  ·
    refine ⟨40602924939459989742041879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27068616626306659828027919 40602924939459989742041879)
    ·
      refine ⟨60904387409189984613062819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40602924939459989742041879 60904387409189984613062819)
      ·
        refine ⟨91356581113784976919594229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60904387409189984613062819 91356581113784976919594229)
        ·
          refine ⟨8564679479417341586211959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91356581113784976919594229 8564679479417341586211959)
          ·
            refine ⟨12847019219126012379317939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564679479417341586211959 12847019219126012379317939)
            ·
              refine ⟨19270528828689018568976909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12847019219126012379317939 19270528828689018568976909)
              ·
                refine ⟨7226448310758381963366341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19270528828689018568976909 7226448310758381963366341)
                ·
                  refine ⟨1354959058267196618131189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7226448310758381963366341 1354959058267196618131189)
                  ·
                    refine ⟨127027411712549682949799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1354959058267196618131189 127027411712549682949799)
                    ·
                      rfl

theorem cell23_742155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 5].length) (baseStart_742155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742155 prefixEnd_742155 := by exact prefixLift 742155
  have htrace : WordTrace (prefixWord ++ tailWord_742155) baseStart_742155 baseEnd_742155 := by
    simpa [prefixWord, tailWord_742155, baseEnd_742155] using wordTrace_append hprefix tailTrace_742155
  have hstable : (prefixWord ++ tailWord_742155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742155).length < 2 ^ (prefixWord ++ tailWord_742155).sum := by decide
  have hdescent : baseEnd_742155 < baseStart_742155 := by decide
  rcases family_descends (prefixWord ++ tailWord_742155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742165 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_742165 : Nat := 118140960795 + 742165 * 2 ^ 59
def prefixEnd_742165 : Nat := 4983230072969 + 3 ^ 40 * 742165 * 2
def baseEnd_742165 : Nat := 381087369944194009724351

theorem tailTrace_742165 : CollatzResearch.WordTrace tailWord_742165 prefixEnd_742165 381087369944194009724351 := by
  unfold tailWord_742165
  simp only [CollatzResearch.WordTrace]
  refine ⟨27068981356270431535891949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18045987570846954357261299 27068981356270431535891949)
  ·
    refine ⟨10150868008601411825959481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27068981356270431535891949 10150868008601411825959481)
    ·
      refine ⟨7613151006451058869469611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10150868008601411825959481 7613151006451058869469611)
      ·
        refine ⟨11419726509676588304204417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7613151006451058869469611 11419726509676588304204417)
        ·
          refine ⟨8564794882257441228153313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11419726509676588304204417 8564794882257441228153313)
          ·
            refine ⟨6423596161693080921114985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8564794882257441228153313 6423596161693080921114985)
            ·
              refine ⟨4817697121269810690836239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6423596161693080921114985 4817697121269810690836239)
              ·
                refine ⟨7226545681904716036254359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817697121269810690836239 7226545681904716036254359)
                ·
                  refine ⟨10839818522857074054381539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226545681904716036254359 10839818522857074054381539)
                  ·
                    refine ⟨16259727784285611081572309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10839818522857074054381539 16259727784285611081572309)
                    ·
                      refine ⟨381087369944194009724351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16259727784285611081572309 381087369944194009724351)
                      ·
                        rfl

theorem cell23_742165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_742165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742165 prefixEnd_742165 := by exact prefixLift 742165
  have htrace : WordTrace (prefixWord ++ tailWord_742165) baseStart_742165 baseEnd_742165 := by
    simpa [prefixWord, tailWord_742165, baseEnd_742165] using wordTrace_append hprefix tailTrace_742165
  have hstable : (prefixWord ++ tailWord_742165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742165).length < 2 ^ (prefixWord ++ tailWord_742165).sum := by decide
  have hdescent : baseEnd_742165 < baseStart_742165 := by decide
  rcases family_descends (prefixWord ++ tailWord_742165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742192 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 1, 6, 2]
def baseStart_742192 : Nat := 118140960795 + 742192 * 2 ^ 59
def prefixEnd_742192 : Nat := 4983230072969 + 3 ^ 40 * 742192 * 2
def baseEnd_742192 : Nat := 381101233921865404086727

theorem tailTrace_742192 : CollatzResearch.WordTrace tailWord_742192 prefixEnd_742192 381101233921865404086727 := by
  unfold tailWord_742192
  simp only [CollatzResearch.WordTrace]
  refine ⟨13534983063586307573562415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18046644084781743431416553 13534983063586307573562415)
  ·
    refine ⟨20302474595379461360343623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13534983063586307573562415 20302474595379461360343623)
    ·
      refine ⟨30453711893069192040515435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20302474595379461360343623 30453711893069192040515435)
      ·
        refine ⟨45680567839603788060773153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30453711893069192040515435 45680567839603788060773153)
        ·
          refine ⟨34260425879702841045579865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45680567839603788060773153 34260425879702841045579865)
          ·
            refine ⟨25695319409777130784184899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34260425879702841045579865 25695319409777130784184899)
            ·
              refine ⟨38542979114665696176277349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25695319409777130784184899 38542979114665696176277349)
              ·
                refine ⟨7226808583999818033052003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38542979114665696176277349 7226808583999818033052003)
                ·
                  refine ⟨10840212875999727049578005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7226808583999818033052003 10840212875999727049578005)
                  ·
                    refine ⟨508134978562487205448969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10840212875999727049578005 508134978562487205448969)
                    ·
                      refine ⟨381101233921865404086727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508134978562487205448969 381101233921865404086727)
                      ·
                        rfl

theorem cell23_742192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 6, 2].length) (baseStart_742192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742192 prefixEnd_742192 := by exact prefixLift 742192
  have htrace : WordTrace (prefixWord ++ tailWord_742192) baseStart_742192 baseEnd_742192 := by
    simpa [prefixWord, tailWord_742192, baseEnd_742192] using wordTrace_append hprefix tailTrace_742192
  have hstable : (prefixWord ++ tailWord_742192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742192).length < 2 ^ (prefixWord ++ tailWord_742192).sum := by decide
  have hdescent : baseEnd_742192 < baseStart_742192 := by decide
  rcases family_descends (prefixWord ++ tailWord_742192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742255 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 7]
def baseStart_742255 : Nat := 118140960795 + 742255 * 2 ^ 59
def prefixEnd_742255 : Nat := 4983230072969 + 3 ^ 40 * 742255 * 2
def baseEnd_742255 : Nat := 381133583203098657598937

theorem tailTrace_742255 : CollatzResearch.WordTrace tailWord_742255 prefixEnd_742255 381133583203098657598937 := by
  unfold tailWord_742255
  simp only [CollatzResearch.WordTrace]
  refine ⟨27072263925944376906668219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18048175950629584604445479 27072263925944376906668219)
  ·
    refine ⟨40608395888916565360002329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27072263925944376906668219 40608395888916565360002329)
    ·
      refine ⟨30456296916687424020001747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40608395888916565360002329 30456296916687424020001747)
      ·
        refine ⟨45684445375031136030002621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30456296916687424020001747 45684445375031136030002621)
        ·
          refine ⟨17131667015636676011250983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45684445375031136030002621 17131667015636676011250983)
          ·
            refine ⟨25697500523455014016876475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17131667015636676011250983 25697500523455014016876475)
            ·
              refine ⟨38546250785182521025314713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25697500523455014016876475 38546250785182521025314713)
              ·
                refine ⟨28909688088886890768986035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38546250785182521025314713 28909688088886890768986035)
                ·
                  refine ⟨43364532133330336153479053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28909688088886890768986035 43364532133330336153479053)
                  ·
                    refine ⟨16261699549998876057554645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43364532133330336153479053 16261699549998876057554645)
                    ·
                      refine ⟨381133583203098657598937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16261699549998876057554645 381133583203098657598937)
                      ·
                        rfl

theorem cell23_742255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_742255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742255 prefixEnd_742255 := by exact prefixLift 742255
  have htrace : WordTrace (prefixWord ++ tailWord_742255) baseStart_742255 baseEnd_742255 := by
    simpa [prefixWord, tailWord_742255, baseEnd_742255] using wordTrace_append hprefix tailTrace_742255
  have hstable : (prefixWord ++ tailWord_742255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742255).length < 2 ^ (prefixWord ++ tailWord_742255).sum := by decide
  have hdescent : baseEnd_742255 < baseStart_742255 := by decide
  rcases family_descends (prefixWord ++ tailWord_742255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742270 : List Nat := [4, 2, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_742270 : Nat := 118140960795 + 742270 * 2 ^ 59
def prefixEnd_742270 : Nat := 4983230072969 + 3 ^ 40 * 742270 * 2
def baseEnd_742270 : Nat := 127047095137638699637123

theorem tailTrace_742270 : CollatzResearch.WordTrace tailWord_742270 prefixEnd_742270 127047095137638699637123 := by
  unfold tailWord_742270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384101377611254308558033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18048540680593356312309509 3384101377611254308558033)
  ·
    refine ⟨2538076033208440731418525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3384101377611254308558033 2538076033208440731418525)
    ·
      refine ⟨951778512453165274281947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2538076033208440731418525 951778512453165274281947)
      ·
        refine ⟨1427667768679747911422921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951778512453165274281947 1427667768679747911422921)
        ·
          refine ⟨1070750826509810933567191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1427667768679747911422921 1070750826509810933567191)
          ·
            refine ⟨1606126239764716400350787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070750826509810933567191 1606126239764716400350787)
            ·
              refine ⟨2409189359647074600526181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606126239764716400350787 2409189359647074600526181)
              ·
                refine ⟨451723004933826487598659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2409189359647074600526181 451723004933826487598659)
                ·
                  refine ⟨677584507400739731397989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451723004933826487598659 677584507400739731397989)
                  ·
                    refine ⟨127047095137638699637123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 677584507400739731397989 127047095137638699637123)
                    ·
                      rfl

theorem cell23_742270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_742270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742270 prefixEnd_742270 := by exact prefixLift 742270
  have htrace : WordTrace (prefixWord ++ tailWord_742270) baseStart_742270 baseEnd_742270 := by
    simpa [prefixWord, tailWord_742270, baseEnd_742270] using wordTrace_append hprefix tailTrace_742270
  have hstable : (prefixWord ++ tailWord_742270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742270).length < 2 ^ (prefixWord ++ tailWord_742270).sum := by decide
  have hdescent : baseEnd_742270 < baseStart_742270 := by decide
  rcases family_descends (prefixWord ++ tailWord_742270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742303 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 2, 3, 2]
def baseStart_742303 : Nat := 118140960795 + 742303 * 2 ^ 59
def prefixEnd_742303 : Nat := 4983230072969 + 3 ^ 40 * 742303 * 2
def baseEnd_742303 : Nat := 381158230274514469798717

theorem tailTrace_742303 : CollatzResearch.WordTrace tailWord_742303 prefixEnd_742303 381158230274514469798717 := by
  unfold tailWord_742303
  simp only [CollatzResearch.WordTrace]
  refine ⟨27074014629770481104415563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18049343086513654069610375 27074014629770481104415563)
  ·
    refine ⟨40611021944655721656623345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27074014629770481104415563 40611021944655721656623345)
    ·
      refine ⟨30458266458491791242467509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40611021944655721656623345 30458266458491791242467509)
      ·
        refine ⟨2855462480483605428981329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30458266458491791242467509 2855462480483605428981329)
        ·
          refine ⟨2141596860362704071735997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2855462480483605428981329 2141596860362704071735997)
          ·
            refine ⟨803098822636014026900999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2141596860362704071735997 803098822636014026900999)
            ·
              refine ⟨1204648233954021040351499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803098822636014026900999 1204648233954021040351499)
              ·
                refine ⟨1806972350931031560527249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204648233954021040351499 1806972350931031560527249)
                ·
                  refine ⟨1355229263198273670395437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1806972350931031560527249 1355229263198273670395437)
                  ·
                    refine ⟨508210973699352626398289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355229263198273670395437 508210973699352626398289)
                    ·
                      refine ⟨381158230274514469798717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508210973699352626398289 381158230274514469798717)
                      ·
                        rfl

theorem cell23_742303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_742303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742303 prefixEnd_742303 := by exact prefixLift 742303
  have htrace : WordTrace (prefixWord ++ tailWord_742303) baseStart_742303 baseEnd_742303 := by
    simpa [prefixWord, tailWord_742303, baseEnd_742303] using wordTrace_append hprefix tailTrace_742303
  have hstable : (prefixWord ++ tailWord_742303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742303).length < 2 ^ (prefixWord ++ tailWord_742303).sum := by decide
  have hdescent : baseEnd_742303 < baseStart_742303 := by decide
  rcases family_descends (prefixWord ++ tailWord_742303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742356 : List Nat := [2, 4, 1, 2, 1, 4, 2, 7]
def baseStart_742356 : Nat := 118140960795 + 742356 * 2 ^ 59
def prefixEnd_742356 : Nat := 4983230072969 + 3 ^ 40 * 742356 * 2
def baseEnd_742356 : Nat := 14117979435155657867999

theorem tailTrace_742356 : CollatzResearch.WordTrace tailWord_742356 prefixEnd_742356 14117979435155657867999 := by
  unfold tailWord_742356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13537973849289235578047461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18050631799052314104063281 13537973849289235578047461)
  ·
    refine ⟨2538370096741731670883899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13537973849289235578047461 2538370096741731670883899)
    ·
      refine ⟨3807555145112597506325849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538370096741731670883899 3807555145112597506325849)
      ·
        refine ⟨2855666358834448129744387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3807555145112597506325849 2855666358834448129744387)
        ·
          refine ⟨4283499538251672194616581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855666358834448129744387 4283499538251672194616581)
          ·
            refine ⟨803156163422188536490609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4283499538251672194616581 803156163422188536490609)
            ·
              refine ⟨602367122566641402367957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803156163422188536490609 602367122566641402367957)
              ·
                refine ⟨14117979435155657867999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 602367122566641402367957 14117979435155657867999)
                ·
                  rfl

theorem cell23_742356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 7].length) (baseStart_742356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742356 prefixEnd_742356 := by exact prefixLift 742356
  have htrace : WordTrace (prefixWord ++ tailWord_742356) baseStart_742356 baseEnd_742356 := by
    simpa [prefixWord, tailWord_742356, baseEnd_742356] using wordTrace_append hprefix tailTrace_742356
  have hstable : (prefixWord ++ tailWord_742356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742356).length < 2 ^ (prefixWord ++ tailWord_742356).sum := by decide
  have hdescent : baseEnd_742356 < baseStart_742356 := by decide
  rcases family_descends (prefixWord ++ tailWord_742356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742367 : List Nat := [1, 1, 2, 3, 5, 2, 1, 3, 1, 2, 2]
def baseStart_742367 : Nat := 118140960795 + 742367 * 2 ^ 59
def prefixEnd_742367 : Nat := 4983230072969 + 3 ^ 40 * 742367 * 2
def baseEnd_742367 : Nat := 381191093036402219398423

theorem tailTrace_742367 : CollatzResearch.WordTrace tailWord_742367 prefixEnd_742367 381191093036402219398423 := by
  unfold tailWord_742367
  simp only [CollatzResearch.WordTrace]
  refine ⟨27076348901538620034745355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18050899267692413356496903 27076348901538620034745355)
  ·
    refine ⟨40614523352307930052118033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27076348901538620034745355 40614523352307930052118033)
    ·
      refine ⟨30460892514230947539088525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40614523352307930052118033 30460892514230947539088525)
      ·
        refine ⟨11422834692836605327158197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30460892514230947539088525 11422834692836605327158197)
        ·
          refine ⟨1070890752453431749421081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11422834692836605327158197 1070890752453431749421081)
          ·
            refine ⟨803168064340073812065811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070890752453431749421081 803168064340073812065811)
            ·
              refine ⟨1204752096510110718098717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803168064340073812065811 1204752096510110718098717)
              ·
                refine ⟨451782036191291519287019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204752096510110718098717 451782036191291519287019)
                ·
                  refine ⟨677673054286937278930529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451782036191291519287019 677673054286937278930529)
                  ·
                    refine ⟨508254790715202959197897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 677673054286937278930529 508254790715202959197897)
                    ·
                      refine ⟨381191093036402219398423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508254790715202959197897 381191093036402219398423)
                      ·
                        rfl

theorem cell23_742367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_742367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742367 prefixEnd_742367 := by exact prefixLift 742367
  have htrace : WordTrace (prefixWord ++ tailWord_742367) baseStart_742367 baseEnd_742367 := by
    simpa [prefixWord, tailWord_742367, baseEnd_742367] using wordTrace_append hprefix tailTrace_742367
  have hstable : (prefixWord ++ tailWord_742367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742367).length < 2 ^ (prefixWord ++ tailWord_742367).sum := by decide
  have hdescent : baseEnd_742367 < baseStart_742367 := by decide
  rcases family_descends (prefixWord ++ tailWord_742367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742392 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_742392 : Nat := 118140960795 + 742392 * 2 ^ 59
def prefixEnd_742392 : Nat := 4983230072969 + 3 ^ 40 * 742392 * 2
def baseEnd_742392 : Nat := 381203930052764621585807

theorem tailTrace_742392 : CollatzResearch.WordTrace tailWord_742392 prefixEnd_742392 381203930052764621585807 := by
  unfold tailWord_742392
  simp only [CollatzResearch.WordTrace]
  refine ⟨13538630363224024652202715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18051507150965366202936953 13538630363224024652202715)
  ·
    refine ⟨20307945544836036978304073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13538630363224024652202715 20307945544836036978304073)
    ·
      refine ⟨15230959158627027733728055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20307945544836036978304073 15230959158627027733728055)
      ·
        refine ⟨22846438737940541600592083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15230959158627027733728055 22846438737940541600592083)
        ·
          refine ⟨34269658106910812400888125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22846438737940541600592083 34269658106910812400888125)
          ·
            refine ⟨12851121790091554650333047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34269658106910812400888125 12851121790091554650333047)
            ·
              refine ⟨19276682685137331975499571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12851121790091554650333047 19276682685137331975499571)
              ·
                refine ⟨28915024027705997963249357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19276682685137331975499571 28915024027705997963249357)
                ·
                  refine ⟨10843134010389749236218509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28915024027705997963249357 10843134010389749236218509)
                  ·
                    refine ⟨4066175253896155963581941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10843134010389749236218509 4066175253896155963581941)
                    ·
                      refine ⟨381203930052764621585807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4066175253896155963581941 381203930052764621585807)
                      ·
                        rfl

theorem cell23_742392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_742392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742392 prefixEnd_742392 := by exact prefixLift 742392
  have htrace : WordTrace (prefixWord ++ tailWord_742392) baseStart_742392 baseEnd_742392 := by
    simpa [prefixWord, tailWord_742392, baseEnd_742392] using wordTrace_append hprefix tailTrace_742392
  have hstable : (prefixWord ++ tailWord_742392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742392).length < 2 ^ (prefixWord ++ tailWord_742392).sum := by decide
  have hdescent : baseEnd_742392 < baseStart_742392 := by decide
  rcases family_descends (prefixWord ++ tailWord_742392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742410 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_742410 : Nat := 118140960795 + 742410 * 2 ^ 59
def prefixEnd_742410 : Nat := 4983230072969 + 3 ^ 40 * 742410 * 2
def baseEnd_742410 : Nat := 381213172704545551160725

theorem tailTrace_742410 : CollatzResearch.WordTrace tailWord_742410 prefixEnd_742410 381213172704545551160725 := by
  unfold tailWord_742410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769479310095709594640171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18051944826921892252373789 6769479310095709594640171)
  ·
    refine ⟨10154218965143564391960257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6769479310095709594640171 10154218965143564391960257)
    ·
      refine ⟨7615664223857673293970193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10154218965143564391960257 7615664223857673293970193)
      ·
        refine ⟨5711748167893254970477645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7615664223857673293970193 5711748167893254970477645)
        ·
          refine ⟨2141905562959970613929117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5711748167893254970477645 2141905562959970613929117)
          ·
            refine ⟨803214586109988980223419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2141905562959970613929117 803214586109988980223419)
            ·
              refine ⟨1204821879164983470335129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803214586109988980223419 1204821879164983470335129)
              ·
                refine ⟨903616409373737602751347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204821879164983470335129 903616409373737602751347)
                ·
                  refine ⟨1355424614060606404127021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903616409373737602751347 1355424614060606404127021)
                  ·
                    refine ⟨508284230272727401547633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355424614060606404127021 508284230272727401547633)
                    ·
                      refine ⟨381213172704545551160725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508284230272727401547633 381213172704545551160725)
                      ·
                        rfl

theorem cell23_742410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_742410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742410 prefixEnd_742410 := by exact prefixLift 742410
  have htrace : WordTrace (prefixWord ++ tailWord_742410) baseStart_742410 baseEnd_742410 := by
    simpa [prefixWord, tailWord_742410, baseEnd_742410] using wordTrace_append hprefix tailTrace_742410
  have hstable : (prefixWord ++ tailWord_742410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742410).length < 2 ^ (prefixWord ++ tailWord_742410).sum := by decide
  have hdescent : baseEnd_742410 < baseStart_742410 := by decide
  rcases family_descends (prefixWord ++ tailWord_742410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742423 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 1, 4, 2]
def baseStart_742423 : Nat := 118140960795 + 742423 * 2 ^ 59
def prefixEnd_742423 : Nat := 4983230072969 + 3 ^ 40 * 742423 * 2
def baseEnd_742423 : Nat := 381219847953054000298165

theorem tailTrace_742423 : CollatzResearch.WordTrace tailWord_742423 prefixEnd_742423 381219847953054000298165 := by
  unfold tailWord_742423
  simp only [CollatzResearch.WordTrace]
  refine ⟨27078391389335741598783923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18052260926223827732522615 27078391389335741598783923)
  ·
    refine ⟨40617587084003612398175885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27078391389335741598783923 40617587084003612398175885)
    ·
      refine ⟨15231595156501354649315957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40617587084003612398175885 15231595156501354649315957)
      ·
        refine ⟨1427962045922001998373371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15231595156501354649315957 1427962045922001998373371)
        ·
          refine ⟨2141943068883002997560057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427962045922001998373371 2141943068883002997560057)
          ·
            refine ⟨1606457301662252248170043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2141943068883002997560057 1606457301662252248170043)
            ·
              refine ⟨2409685952493378372255065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606457301662252248170043 2409685952493378372255065)
              ·
                refine ⟨1807264464370033779191299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409685952493378372255065 1807264464370033779191299)
                ·
                  refine ⟨2710896696555050668786949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807264464370033779191299 2710896696555050668786949)
                  ·
                    refine ⟨508293130604072000397553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2710896696555050668786949 508293130604072000397553)
                    ·
                      refine ⟨381219847953054000298165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508293130604072000397553 381219847953054000298165)
                      ·
                        rfl

theorem cell23_742423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_742423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742423 prefixEnd_742423 := by exact prefixLift 742423
  have htrace : WordTrace (prefixWord ++ tailWord_742423) baseStart_742423 baseEnd_742423 := by
    simpa [prefixWord, tailWord_742423, baseEnd_742423] using wordTrace_append hprefix tailTrace_742423
  have hstable : (prefixWord ++ tailWord_742423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742423).length < 2 ^ (prefixWord ++ tailWord_742423).sum := by decide
  have hdescent : baseEnd_742423 < baseStart_742423 := by decide
  rcases family_descends (prefixWord ++ tailWord_742423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742456 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_742456 : Nat := 118140960795 + 742456 * 2 ^ 59
def prefixEnd_742456 : Nat := 4983230072969 + 3 ^ 40 * 742456 * 2
def baseEnd_742456 : Nat := 381236792814652371185513

theorem tailTrace_742456 : CollatzResearch.WordTrace tailWord_742456 prefixEnd_742456 381236792814652371185513 := by
  unfold tailWord_742456
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539797499108094117367611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18053063332144125489823481 13539797499108094117367611)
  ·
    refine ⟨20309696248662141176051417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13539797499108094117367611 20309696248662141176051417)
    ·
      refine ⟨15232272186496605882038563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20309696248662141176051417 15232272186496605882038563)
      ·
        refine ⟨22848408279744908823057845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15232272186496605882038563 22848408279744908823057845)
        ·
          refine ⟨2142038276226085202161673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22848408279744908823057845 2142038276226085202161673)
          ·
            refine ⟨1606528707169563901621255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142038276226085202161673 1606528707169563901621255)
            ·
              refine ⟨2409793060754345852431883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606528707169563901621255 2409793060754345852431883)
              ·
                refine ⟨3614689591131518778647825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2409793060754345852431883 3614689591131518778647825)
                ·
                  refine ⟨2711017193348639083985869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3614689591131518778647825 2711017193348639083985869)
                  ·
                    refine ⟨1016631447505739656494701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711017193348639083985869 1016631447505739656494701)
                    ·
                      refine ⟨381236792814652371185513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1016631447505739656494701 381236792814652371185513)
                      ·
                        rfl

theorem cell23_742456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_742456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742456 prefixEnd_742456 := by exact prefixLift 742456
  have htrace : WordTrace (prefixWord ++ tailWord_742456) baseStart_742456 baseEnd_742456 := by
    simpa [prefixWord, tailWord_742456, baseEnd_742456] using wordTrace_append hprefix tailTrace_742456
  have hstable : (prefixWord ++ tailWord_742456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742456).length < 2 ^ (prefixWord ++ tailWord_742456).sum := by decide
  have hdescent : baseEnd_742456 < baseStart_742456 := by decide
  rcases family_descends (prefixWord ++ tailWord_742456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742496 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 4, 4, 2]
def baseStart_742496 : Nat := 118140960795 + 742496 * 2 ^ 59
def prefixEnd_742496 : Nat := 4983230072969 + 3 ^ 40 * 742496 * 2
def baseEnd_742496 : Nat := 381257332040832214685329

theorem tailTrace_742496 : CollatzResearch.WordTrace tailWord_742496 prefixEnd_742496 381257332040832214685329 := by
  unfold tailWord_742496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13540526959035637533095671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18054035945380850044127561 13540526959035637533095671)
  ·
    refine ⟨20310790438553456299643507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13540526959035637533095671 20310790438553456299643507)
    ·
      refine ⟨30466185657830184449465261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20310790438553456299643507 30466185657830184449465261)
      ·
        refine ⟨11424819621686319168549473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30466185657830184449465261 11424819621686319168549473)
        ·
          refine ⟨8568614716264739376412105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11424819621686319168549473 8568614716264739376412105)
          ·
            refine ⟨6426461037198554532309079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8568614716264739376412105 6426461037198554532309079)
            ·
              refine ⟨9639691555797831798463619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6426461037198554532309079 9639691555797831798463619)
              ·
                refine ⟨14459537333696747697695429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9639691555797831798463619 14459537333696747697695429)
                ·
                  refine ⟨2711163250068140193317893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14459537333696747697695429 2711163250068140193317893)
                  ·
                    refine ⟨508343109387776286247105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2711163250068140193317893 508343109387776286247105)
                    ·
                      refine ⟨381257332040832214685329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508343109387776286247105 381257332040832214685329)
                      ·
                        rfl

theorem cell23_742496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_742496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742496 prefixEnd_742496 := by exact prefixLift 742496
  have htrace : WordTrace (prefixWord ++ tailWord_742496) baseStart_742496 baseEnd_742496 := by
    simpa [prefixWord, tailWord_742496, baseEnd_742496] using wordTrace_append hprefix tailTrace_742496
  have hstable : (prefixWord ++ tailWord_742496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742496).length < 2 ^ (prefixWord ++ tailWord_742496).sum := by decide
  have hdescent : baseEnd_742496 < baseStart_742496 := by decide
  rcases family_descends (prefixWord ++ tailWord_742496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742570 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 6]
def baseStart_742570 : Nat := 118140960795 + 742570 * 2 ^ 59
def prefixEnd_742570 : Nat := 4983230072969 + 3 ^ 40 * 742570 * 2
def baseEnd_742570 : Nat := 42366147734362769462221

theorem tailTrace_742570 : CollatzResearch.WordTrace tailWord_742570 prefixEnd_742570 42366147734362769462221 := by
  unfold tailWord_742570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770938229950796426096291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18055835279868790469590109 6770938229950796426096291)
  ·
    refine ⟨10156407344926194639144437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6770938229950796426096291 10156407344926194639144437)
    ·
      refine ⟨952163188586830747419791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10156407344926194639144437 952163188586830747419791)
      ·
        refine ⟨1428244782880246121129687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 952163188586830747419791 1428244782880246121129687)
        ·
          refine ⟨2142367174320369181694531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428244782880246121129687 2142367174320369181694531)
          ·
            refine ⟨3213550761480553772541797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142367174320369181694531 3213550761480553772541797)
            ·
              refine ⟨602540767777603832351587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3213550761480553772541797 602540767777603832351587)
              ·
                refine ⟨903811151666405748527381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602540767777603832351587 903811151666405748527381)
                ·
                  refine ⟨42366147734362769462221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 903811151666405748527381 42366147734362769462221)
                  ·
                    rfl

theorem cell23_742570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_742570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742570 prefixEnd_742570 := by exact prefixLift 742570
  have htrace : WordTrace (prefixWord ++ tailWord_742570) baseStart_742570 baseEnd_742570 := by
    simpa [prefixWord, tailWord_742570, baseEnd_742570] using wordTrace_append hprefix tailTrace_742570
  have hstable : (prefixWord ++ tailWord_742570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742570).length < 2 ^ (prefixWord ++ tailWord_742570).sum := by decide
  have hdescent : baseEnd_742570 < baseStart_742570 := by decide
  rcases family_descends (prefixWord ++ tailWord_742570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742590 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_742590 : Nat := 118140960795 + 742590 * 2 ^ 59
def prefixEnd_742590 : Nat := 4983230072969 + 3 ^ 40 * 742590 * 2
def baseEnd_742590 : Nat := 381305599222354846909897

theorem tailTrace_742590 : CollatzResearch.WordTrace tailWord_742590 prefixEnd_742590 381305599222354846909897 := by
  unfold tailWord_742590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385560297466341140014153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18056321586487152746742149 3385560297466341140014153)
  ·
    refine ⟨2539170223099755855010615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3385560297466341140014153 2539170223099755855010615)
    ·
      refine ⟨3808755334649633782515923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539170223099755855010615 3808755334649633782515923)
      ·
        refine ⟨5713133001974450673773885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3808755334649633782515923 5713133001974450673773885)
        ·
          refine ⟨2142424875740419002665207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5713133001974450673773885 2142424875740419002665207)
          ·
            refine ⟨3213637313610628503997811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142424875740419002665207 3213637313610628503997811)
            ·
              refine ⟨4820455970415942755996717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213637313610628503997811 4820455970415942755996717)
              ·
                refine ⟨1807670988905978533498769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4820455970415942755996717 1807670988905978533498769)
                ·
                  refine ⟨1355753241679483900124077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807670988905978533498769 1355753241679483900124077)
                  ·
                    refine ⟨508407465629806462546529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355753241679483900124077 508407465629806462546529)
                    ·
                      refine ⟨381305599222354846909897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508407465629806462546529 381305599222354846909897)
                      ·
                        rfl

theorem cell23_742590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_742590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742590 prefixEnd_742590 := by exact prefixLift 742590
  have htrace : WordTrace (prefixWord ++ tailWord_742590) baseStart_742590 baseEnd_742590 := by
    simpa [prefixWord, tailWord_742590, baseEnd_742590] using wordTrace_append hprefix tailTrace_742590
  have hstable : (prefixWord ++ tailWord_742590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742590).length < 2 ^ (prefixWord ++ tailWord_742590).sum := by decide
  have hdescent : baseEnd_742590 < baseStart_742590 := by decide
  rcases family_descends (prefixWord ++ tailWord_742590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742603 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 7, 2, 2]
def baseStart_742603 : Nat := 118140960795 + 742603 * 2 ^ 59
def prefixEnd_742603 : Nat := 4983230072969 + 3 ^ 40 * 742603 * 2
def baseEnd_742603 : Nat := 381312274470863296047337

theorem tailTrace_742603 : CollatzResearch.WordTrace tailWord_742603 prefixEnd_742603 381312274470863296047337 := by
  unfold tailWord_742603
  simp only [CollatzResearch.WordTrace]
  refine ⟨27084956528683632340336463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18056637685789088226890975 27084956528683632340336463)
  ·
    refine ⟨40627434793025448510504695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27084956528683632340336463 40627434793025448510504695)
    ·
      refine ⟨60941152189538172765757043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40627434793025448510504695 60941152189538172765757043)
      ·
        refine ⟨91411728284307259148635565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60941152189538172765757043 91411728284307259148635565)
        ·
          refine ⟨34279398106615222180738337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91411728284307259148635565 34279398106615222180738337)
          ·
            refine ⟨25709548579961416635553753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34279398106615222180738337 25709548579961416635553753)
            ·
              refine ⟨19282161434971062476665315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25709548579961416635553753 19282161434971062476665315)
              ·
                refine ⟨28923242152456593714997973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19282161434971062476665315 28923242152456593714997973)
                ·
                  refine ⟨677888487948201415195265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 28923242152456593714997973 677888487948201415195265)
                  ·
                    refine ⟨508416365961151061396449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 677888487948201415195265 508416365961151061396449)
                    ·
                      refine ⟨381312274470863296047337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508416365961151061396449 381312274470863296047337)
                      ·
                        rfl

theorem cell23_742603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 2, 2].length) (baseStart_742603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742603 prefixEnd_742603 := by exact prefixLift 742603
  have htrace : WordTrace (prefixWord ++ tailWord_742603) baseStart_742603 baseEnd_742603 := by
    simpa [prefixWord, tailWord_742603, baseEnd_742603] using wordTrace_append hprefix tailTrace_742603
  have hstable : (prefixWord ++ tailWord_742603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742603).length < 2 ^ (prefixWord ++ tailWord_742603).sum := by decide
  have hdescent : baseEnd_742603 < baseStart_742603 := by decide
  rcases family_descends (prefixWord ++ tailWord_742603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742637 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_742637 : Nat := 118140960795 + 742637 * 2 ^ 59
def prefixEnd_742637 : Nat := 4983230072969 + 3 ^ 40 * 742637 * 2
def baseEnd_742637 : Nat := 381329732813116163022181

theorem tailTrace_742637 : CollatzResearch.WordTrace tailWord_742637 prefixEnd_742637 381329732813116163022181 := by
  unfold tailWord_742637
  simp only [CollatzResearch.WordTrace]
  refine ⟨27086196610560456147074165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18057464407040304098049443 27086196610560456147074165)
  ·
    refine ⟨2539330932240042763788203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27086196610560456147074165 2539330932240042763788203)
    ·
      refine ⟨3808996398360064145682305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539330932240042763788203 3808996398360064145682305)
      ·
        refine ⟨2856747298770048109261729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3808996398360064145682305 2856747298770048109261729)
        ·
          refine ⟨2142560474077536081946297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856747298770048109261729 2142560474077536081946297)
          ·
            refine ⟨1606920355558152061459723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2142560474077536081946297 1606920355558152061459723)
            ·
              refine ⟨2410380533337228092189585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606920355558152061459723 2410380533337228092189585)
              ·
                refine ⟨1807785400002921069142189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410380533337228092189585 1807785400002921069142189)
                ·
                  refine ⟨677919525001095400928321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1807785400002921069142189 677919525001095400928321)
                  ·
                    refine ⟨508439643750821550696241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 677919525001095400928321 508439643750821550696241)
                    ·
                      refine ⟨381329732813116163022181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508439643750821550696241 381329732813116163022181)
                      ·
                        rfl

theorem cell23_742637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_742637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742637 prefixEnd_742637 := by exact prefixLift 742637
  have htrace : WordTrace (prefixWord ++ tailWord_742637) baseStart_742637 baseEnd_742637 := by
    simpa [prefixWord, tailWord_742637, baseEnd_742637] using wordTrace_append hprefix tailTrace_742637
  have hstable : (prefixWord ++ tailWord_742637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742637).length < 2 ^ (prefixWord ++ tailWord_742637).sum := by decide
  have hdescent : baseEnd_742637 < baseStart_742637 := by decide
  rcases family_descends (prefixWord ++ tailWord_742637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742654 : List Nat := [4, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_742654 : Nat := 118140960795 + 742654 * 2 ^ 59
def prefixEnd_742654 : Nat := 4983230072969 + 3 ^ 40 * 742654 * 2
def baseEnd_742654 : Nat := 381338461984242596509603

theorem tailTrace_742654 : CollatzResearch.WordTrace tailWord_742654 prefixEnd_742654 381338461984242596509603 := by
  unfold tailWord_742654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385852081437358506305377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18057877767665912033628677 3385852081437358506305377)
  ·
    refine ⟨2539389061078018879729033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3385852081437358506305377 2539389061078018879729033)
    ·
      refine ⟨1904541795808514159796775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2539389061078018879729033 1904541795808514159796775)
      ·
        refine ⟨2856812693712771239695163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904541795808514159796775 2856812693712771239695163)
        ·
          refine ⟨4285219040569156859542745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856812693712771239695163 4285219040569156859542745)
          ·
            refine ⟨3213914280426867644657059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4285219040569156859542745 3213914280426867644657059)
            ·
              refine ⟨4820871420640301466985589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213914280426867644657059 4820871420640301466985589)
              ·
                refine ⟨451956695685028262529899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4820871420640301466985589 451956695685028262529899)
                ·
                  refine ⟨677935043527542393794849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451956695685028262529899 677935043527542393794849)
                  ·
                    refine ⟨508451282645656795346137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 677935043527542393794849 508451282645656795346137)
                    ·
                      refine ⟨381338461984242596509603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508451282645656795346137 381338461984242596509603)
                      ·
                        rfl

theorem cell23_742654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_742654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742654 prefixEnd_742654 := by exact prefixLift 742654
  have htrace : WordTrace (prefixWord ++ tailWord_742654) baseStart_742654 baseEnd_742654 := by
    simpa [prefixWord, tailWord_742654, baseEnd_742654] using wordTrace_append hprefix tailTrace_742654
  have hstable : (prefixWord ++ tailWord_742654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742654).length < 2 ^ (prefixWord ++ tailWord_742654).sum := by decide
  have hdescent : baseEnd_742654 < baseStart_742654 := by decide
  rcases family_descends (prefixWord ++ tailWord_742654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742657 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_742657 : Nat := 118140960795 + 742657 * 2 ^ 59
def prefixEnd_742657 : Nat := 4983230072969 + 3 ^ 40 * 742657 * 2
def baseEnd_742657 : Nat := 381340002426206084772089

theorem tailTrace_742657 : CollatzResearch.WordTrace tailWord_742657 prefixEnd_742657 381340002426206084772089 := by
  unfold tailWord_742657
  simp only [CollatzResearch.WordTrace]
  refine ⟨27086926070487999562802225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18057950713658666375201483 27086926070487999562802225)
  ·
    refine ⟨20315194552865999672101669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27086926070487999562802225 20315194552865999672101669)
    ·
      refine ⟨3809098978662374938519063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20315194552865999672101669 3809098978662374938519063)
      ·
        refine ⟨5713648467993562407778595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809098978662374938519063 5713648467993562407778595)
        ·
          refine ⟨8570472701990343611667893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5713648467993562407778595 8570472701990343611667893)
          ·
            refine ⟨803481815811594713593865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8570472701990343611667893 803481815811594713593865)
            ·
              refine ⟨602611361858696035195399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803481815811594713593865 602611361858696035195399)
              ·
                refine ⟨903917042788044052793099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602611361858696035195399 903917042788044052793099)
                ·
                  refine ⟨1355875564182066079189649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903917042788044052793099 1355875564182066079189649)
                  ·
                    refine ⟨1016906673136549559392237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1355875564182066079189649 1016906673136549559392237)
                    ·
                      refine ⟨381340002426206084772089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1016906673136549559392237 381340002426206084772089)
                      ·
                        rfl

theorem cell23_742657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_742657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742657 prefixEnd_742657 := by exact prefixLift 742657
  have htrace : WordTrace (prefixWord ++ tailWord_742657) baseStart_742657 baseEnd_742657 := by
    simpa [prefixWord, tailWord_742657, baseEnd_742657] using wordTrace_append hprefix tailTrace_742657
  have hstable : (prefixWord ++ tailWord_742657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742657).length < 2 ^ (prefixWord ++ tailWord_742657).sum := by decide
  have hdescent : baseEnd_742657 < baseStart_742657 := by decide
  rcases family_descends (prefixWord ++ tailWord_742657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742670 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_742670 : Nat := 118140960795 + 742670 * 2 ^ 59
def prefixEnd_742670 : Nat := 4983230072969 + 3 ^ 40 * 742670 * 2
def baseEnd_742670 : Nat := 381346677674714533909529

theorem tailTrace_742670 : CollatzResearch.WordTrace tailWord_742670 prefixEnd_742670 381346677674714533909529 := by
  unfold tailWord_742670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385925027430112847878183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18058266812960601855350309 3385925027430112847878183)
  ·
    refine ⟨5078887541145169271817275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3385925027430112847878183 5078887541145169271817275)
    ·
      refine ⟨7618331311717753907725913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5078887541145169271817275 7618331311717753907725913)
      ·
        refine ⟨5713748483788315430794435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7618331311717753907725913 5713748483788315430794435)
        ·
          refine ⟨8570622725682473146191653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5713748483788315430794435 8570622725682473146191653)
          ·
            refine ⟨1606991761065463714910935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8570622725682473146191653 1606991761065463714910935)
            ·
              refine ⟨2410487641598195572366403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606991761065463714910935 2410487641598195572366403)
              ·
                refine ⟨3615731462397293358549605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410487641598195572366403 3615731462397293358549605)
                ·
                  refine ⟨677949649199492504728051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3615731462397293358549605 677949649199492504728051)
                  ·
                    refine ⟨1016924473799238757092077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 677949649199492504728051 1016924473799238757092077)
                    ·
                      refine ⟨381346677674714533909529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1016924473799238757092077 381346677674714533909529)
                      ·
                        rfl

theorem cell23_742670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_742670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742670 prefixEnd_742670 := by exact prefixLift 742670
  have htrace : WordTrace (prefixWord ++ tailWord_742670) baseStart_742670 baseEnd_742670 := by
    simpa [prefixWord, tailWord_742670, baseEnd_742670] using wordTrace_append hprefix tailTrace_742670
  have hstable : (prefixWord ++ tailWord_742670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742670).length < 2 ^ (prefixWord ++ tailWord_742670).sum := by decide
  have hdescent : baseEnd_742670 < baseStart_742670 := by decide
  rcases family_descends (prefixWord ++ tailWord_742670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742687 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 1, 3, 3]
def baseStart_742687 : Nat := 118140960795 + 742687 * 2 ^ 59
def prefixEnd_742687 : Nat := 4983230072969 + 3 ^ 40 * 742687 * 2
def baseEnd_742687 : Nat := 381355406845840967396951

theorem tailTrace_742687 : CollatzResearch.WordTrace tailWord_742687 prefixEnd_742687 381355406845840967396951 := by
  unfold tailWord_742687
  simp only [CollatzResearch.WordTrace]
  refine ⟨27088020260379314686394315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18058680173586209790929543 27088020260379314686394315)
  ·
    refine ⟨40632030390568972029591473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27088020260379314686394315 40632030390568972029591473)
    ·
      refine ⟨30474022792926729022193605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40632030390568972029591473 30474022792926729022193605)
      ·
        refine ⟨5713879273673761691661301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30474022792926729022193605 5713879273673761691661301)
        ·
          refine ⟨535676181906915158593247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5713879273673761691661301 535676181906915158593247)
          ·
            refine ⟨803514272860372737889871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535676181906915158593247 803514272860372737889871)
            ·
              refine ⟨1205271409290559106834807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803514272860372737889871 1205271409290559106834807)
              ·
                refine ⟨1807907113935838660252211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205271409290559106834807 1807907113935838660252211)
                ·
                  refine ⟨2711860670903757990378317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807907113935838660252211 2711860670903757990378317)
                  ·
                    refine ⟨1016947751588909246391869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2711860670903757990378317 1016947751588909246391869)
                    ·
                      refine ⟨381355406845840967396951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1016947751588909246391869 381355406845840967396951)
                      ·
                        rfl

theorem cell23_742687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_742687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742687 prefixEnd_742687 := by exact prefixLift 742687
  have htrace : WordTrace (prefixWord ++ tailWord_742687) baseStart_742687 baseEnd_742687 := by
    simpa [prefixWord, tailWord_742687, baseEnd_742687] using wordTrace_append hprefix tailTrace_742687
  have hstable : (prefixWord ++ tailWord_742687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742687).length < 2 ^ (prefixWord ++ tailWord_742687).sum := by decide
  have hdescent : baseEnd_742687 < baseStart_742687 := by decide
  rcases family_descends (prefixWord ++ tailWord_742687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742746 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_742746 : Nat := 118140960795 + 742746 * 2 ^ 59
def prefixEnd_742746 : Nat := 4983230072969 + 3 ^ 40 * 742746 * 2
def baseEnd_742746 : Nat := 127128567401485412186393

theorem tailTrace_742746 : CollatzResearch.WordTrace tailWord_742746 prefixEnd_742746 127128567401485412186393 := by
  unfold tailWord_742746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6772543041791391940698023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18060114778110378508528061 6772543041791391940698023)
  ·
    refine ⟨10158814562687087911047035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6772543041791391940698023 10158814562687087911047035)
    ·
      refine ⟨15238221844030631866570553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10158814562687087911047035 15238221844030631866570553)
      ·
        refine ⟨11428666383022973899927915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15238221844030631866570553 11428666383022973899927915)
        ·
          refine ⟨17142999574534460849891873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11428666383022973899927915 17142999574534460849891873)
          ·
            refine ⟨12857249680900845637418905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17142999574534460849891873 12857249680900845637418905)
            ·
              refine ⟨9642937260675634228064179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12857249680900845637418905 9642937260675634228064179)
              ·
                refine ⟨14464405891013451342096269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9642937260675634228064179 14464405891013451342096269)
                ·
                  refine ⟨5424152209130044253286101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14464405891013451342096269 5424152209130044253286101)
                  ·
                    refine ⟨127128567401485412186393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5424152209130044253286101 127128567401485412186393)
                    ·
                      rfl

theorem cell23_742746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_742746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742746 prefixEnd_742746 := by exact prefixLift 742746
  have htrace : WordTrace (prefixWord ++ tailWord_742746) baseStart_742746 baseEnd_742746 := by
    simpa [prefixWord, tailWord_742746, baseEnd_742746] using wordTrace_append hprefix tailTrace_742746
  have hstable : (prefixWord ++ tailWord_742746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742746).length < 2 ^ (prefixWord ++ tailWord_742746).sum := by decide
  have hdescent : baseEnd_742746 < baseStart_742746 := by decide
  rcases family_descends (prefixWord ++ tailWord_742746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742810 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_742810 : Nat := 118140960795 + 742810 * 2 ^ 59
def prefixEnd_742810 : Nat := 4983230072969 + 3 ^ 40 * 742810 * 2
def baseEnd_742810 : Nat := 127139521655447995386295

theorem tailTrace_742810 : CollatzResearch.WordTrace tailWord_742810 prefixEnd_742810 127139521655447995386295 := by
  unfold tailWord_742810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6773126609733426673280471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18061670959289137795414589 6773126609733426673280471)
  ·
    refine ⟨10159689914600140009920707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6773126609733426673280471 10159689914600140009920707)
    ·
      refine ⟨15239534871900210014881061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10159689914600140009920707 15239534871900210014881061)
      ·
        refine ⟨2857412788481289377790199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15239534871900210014881061 2857412788481289377790199)
        ·
          refine ⟨4286119182721934066685299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857412788481289377790199 4286119182721934066685299)
          ·
            refine ⟨6429178774082901100027949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286119182721934066685299 6429178774082901100027949)
            ·
              refine ⟨2410942040281087912510481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6429178774082901100027949 2410942040281087912510481)
              ·
                refine ⟨1808206530210815934382861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410942040281087912510481 1808206530210815934382861)
                ·
                  refine ⟨678077448829055975393573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1808206530210815934382861 678077448829055975393573)
                  ·
                    refine ⟨127139521655447995386295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 678077448829055975393573 127139521655447995386295)
                    ·
                      rfl

theorem cell23_742810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_742810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742810 prefixEnd_742810 := by exact prefixLift 742810
  have htrace : WordTrace (prefixWord ++ tailWord_742810) baseStart_742810 baseEnd_742810 := by
    simpa [prefixWord, tailWord_742810, baseEnd_742810] using wordTrace_append hprefix tailTrace_742810
  have hstable : (prefixWord ++ tailWord_742810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742810).length < 2 ^ (prefixWord ++ tailWord_742810).sum := by decide
  have hdescent : baseEnd_742810 < baseStart_742810 := by decide
  rcases family_descends (prefixWord ++ tailWord_742810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742814 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_742814 : Nat := 118140960795 + 742814 * 2 ^ 59
def prefixEnd_742814 : Nat := 4983230072969 + 3 ^ 40 * 742814 * 2
def baseEnd_742814 : Nat := 127140206296320656836289

theorem tailTrace_742814 : CollatzResearch.WordTrace tailWord_742814 prefixEnd_742814 127140206296320656836289 := by
  unfold tailWord_742814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3386581541364901922033437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18061768220612810250844997 3386581541364901922033437)
  ·
    refine ⟨1269968078011838220762539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3386581541364901922033437 1269968078011838220762539)
    ·
      refine ⟨1904952117017757331143809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269968078011838220762539 1904952117017757331143809)
      ·
        refine ⟨1428714087763317998357857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1904952117017757331143809 1428714087763317998357857)
        ·
          refine ⟨1071535565822488498768393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1428714087763317998357857 1071535565822488498768393)
          ·
            refine ⟨803651674366866374076295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1071535565822488498768393 803651674366866374076295)
            ·
              refine ⟨1205477511550299561114443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803651674366866374076295 1205477511550299561114443)
              ·
                refine ⟨1808216267325449341671665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205477511550299561114443 1808216267325449341671665)
                ·
                  refine ⟨1356162200494087006253749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1808216267325449341671665 1356162200494087006253749)
                  ·
                    refine ⟨127140206296320656836289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1356162200494087006253749 127140206296320656836289)
                    ·
                      rfl

theorem cell23_742814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_742814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742814 prefixEnd_742814 := by exact prefixLift 742814
  have htrace : WordTrace (prefixWord ++ tailWord_742814) baseStart_742814 baseEnd_742814 := by
    simpa [prefixWord, tailWord_742814, baseEnd_742814] using wordTrace_append hprefix tailTrace_742814
  have hstable : (prefixWord ++ tailWord_742814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742814).length < 2 ^ (prefixWord ++ tailWord_742814).sum := by decide
  have hdescent : baseEnd_742814 < baseStart_742814 := by decide
  rcases family_descends (prefixWord ++ tailWord_742814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742823 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 8]
def baseStart_742823 : Nat := 118140960795 + 742823 * 2 ^ 59
def prefixEnd_742823 : Nat := 4983230072969 + 3 ^ 40 * 742823 * 2
def baseEnd_742823 : Nat := 42380582246094715032925

theorem tailTrace_742823 : CollatzResearch.WordTrace tailWord_742823 prefixEnd_742823 42380582246094715032925 := by
  unfold tailWord_742823
  simp only [CollatzResearch.WordTrace]
  refine ⟨27092980587886609913345123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18061987058591073275563415 27092980587886609913345123)
  ·
    refine ⟨40639470881829914870017685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27092980587886609913345123 40639470881829914870017685)
    ·
      refine ⟨1904975197585777259532079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40639470881829914870017685 1904975197585777259532079)
      ·
        refine ⟨2857462796378665889298119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904975197585777259532079 2857462796378665889298119)
        ·
          refine ⟨4286194194567998833947179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857462796378665889298119 4286194194567998833947179)
          ·
            refine ⟨6429291291851998250920769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286194194567998833947179 6429291291851998250920769)
            ·
              refine ⟨4821968468888998688190577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6429291291851998250920769 4821968468888998688190577)
              ·
                refine ⟨3616476351666749016142933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4821968468888998688190577 3616476351666749016142933)
                ·
                  refine ⟨42380582246094715032925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3616476351666749016142933 42380582246094715032925)
                  ·
                    rfl

theorem cell23_742823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 8].length) (baseStart_742823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742823 prefixEnd_742823 := by exact prefixLift 742823
  have htrace : WordTrace (prefixWord ++ tailWord_742823) baseStart_742823 baseEnd_742823 := by
    simpa [prefixWord, tailWord_742823, baseEnd_742823] using wordTrace_append hprefix tailTrace_742823
  have hstable : (prefixWord ++ tailWord_742823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742823).length < 2 ^ (prefixWord ++ tailWord_742823).sum := by decide
  have hdescent : baseEnd_742823 < baseStart_742823 := by decide
  rcases family_descends (prefixWord ++ tailWord_742823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742877 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_742877 : Nat := 118140960795 + 742877 * 2 ^ 59
def prefixEnd_742877 : Nat := 4983230072969 + 3 ^ 40 * 742877 * 2
def baseEnd_742877 : Nat := 381452968170195224021077

theorem tailTrace_742877 : CollatzResearch.WordTrace tailWord_742877 prefixEnd_742877 381452968170195224021077 := by
  unfold tailWord_742877
  simp only [CollatzResearch.WordTrace]
  refine ⟨27094950129690977135810885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18063300086460651423873923 27094950129690977135810885)
  ·
    refine ⟨5080303149317058212964541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27094950129690977135810885 5080303149317058212964541)
    ·
      refine ⟨1905113680993896829861703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5080303149317058212964541 1905113680993896829861703)
      ·
        refine ⟨2857670521490845244792555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905113680993896829861703 2857670521490845244792555)
        ·
          refine ⟨4286505782236267867188833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857670521490845244792555 4286505782236267867188833)
          ·
            refine ⟨3214879336677200900391625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4286505782236267867188833 3214879336677200900391625)
            ·
              refine ⟨2411159502507900675293719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3214879336677200900391625 2411159502507900675293719)
              ·
                refine ⟨3616739253761851012940579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411159502507900675293719 3616739253761851012940579)
                ·
                  refine ⟨5425108880642776519410869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616739253761851012940579 5425108880642776519410869)
                  ·
                    refine ⟨508603957560260298694769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5425108880642776519410869 508603957560260298694769)
                    ·
                      refine ⟨381452968170195224021077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508603957560260298694769 381452968170195224021077)
                      ·
                        rfl

theorem cell23_742877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_742877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742877 prefixEnd_742877 := by exact prefixLift 742877
  have htrace : WordTrace (prefixWord ++ tailWord_742877) baseStart_742877 baseEnd_742877 := by
    simpa [prefixWord, tailWord_742877, baseEnd_742877] using wordTrace_append hprefix tailTrace_742877
  have hstable : (prefixWord ++ tailWord_742877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742877).length < 2 ^ (prefixWord ++ tailWord_742877).sum := by decide
  have hdescent : baseEnd_742877 < baseStart_742877 := by decide
  rcases family_descends (prefixWord ++ tailWord_742877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742901 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_742901 : Nat := 118140960795 + 742901 * 2 ^ 59
def prefixEnd_742901 : Nat := 4983230072969 + 3 ^ 40 * 742901 * 2
def baseEnd_742901 : Nat := 381465291705903130120967

theorem tailTrace_742901 : CollatzResearch.WordTrace tailWord_742901 prefixEnd_742901 381465291705903130120967 := by
  unfold tailWord_742901
  simp only [CollatzResearch.WordTrace]
  refine ⟨27095825481604029234684557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18063883654402686156456371 27095825481604029234684557)
  ·
    refine ⟨10160934555601510963006709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27095825481604029234684557 10160934555601510963006709)
    ·
      refine ⟨952587614587641652781879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10160934555601510963006709 952587614587641652781879)
      ·
        refine ⟨1428881421881462479172819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 952587614587641652781879 1428881421881462479172819)
        ·
          refine ⟨2143322132822193718759229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428881421881462479172819 2143322132822193718759229)
          ·
            refine ⟨803745799808322644534711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2143322132822193718759229 803745799808322644534711)
            ·
              refine ⟨1205618699712483966802067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803745799808322644534711 1205618699712483966802067)
              ·
                refine ⟨1808428049568725950203101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205618699712483966802067 1808428049568725950203101)
                ·
                  refine ⟨678160518588272231326163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1808428049568725950203101 678160518588272231326163)
                  ·
                    refine ⟨1017240777882408346989245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 678160518588272231326163 1017240777882408346989245)
                    ·
                      refine ⟨381465291705903130120967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1017240777882408346989245 381465291705903130120967)
                      ·
                        rfl

theorem cell23_742901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_742901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742901 prefixEnd_742901 := by exact prefixLift 742901
  have htrace : WordTrace (prefixWord ++ tailWord_742901) baseStart_742901 baseEnd_742901 := by
    simpa [prefixWord, tailWord_742901, baseEnd_742901] using wordTrace_append hprefix tailTrace_742901
  have hstable : (prefixWord ++ tailWord_742901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742901).length < 2 ^ (prefixWord ++ tailWord_742901).sum := by decide
  have hdescent : baseEnd_742901 < baseStart_742901 := by decide
  rcases family_descends (prefixWord ++ tailWord_742901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742903 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_742903 : Nat := 118140960795 + 742903 * 2 ^ 59
def prefixEnd_742903 : Nat := 4983230072969 + 3 ^ 40 * 742903 * 2
def baseEnd_742903 : Nat := 381466318667212122295957

theorem tailTrace_742903 : CollatzResearch.WordTrace tailWord_742903 prefixEnd_742903 381466318667212122295957 := by
  unfold tailWord_742903
  simp only [CollatzResearch.WordTrace]
  refine ⟨27095898427596783576257363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18063932285064522384171575 27095898427596783576257363)
  ·
    refine ⟨40643847641395175364386045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27095898427596783576257363 40643847641395175364386045)
    ·
      refine ⟨15241442865523190761644767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40643847641395175364386045 15241442865523190761644767)
      ·
        refine ⟨22862164298284786142467151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15241442865523190761644767 22862164298284786142467151)
        ·
          refine ⟨34293246447427179213700727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22862164298284786142467151 34293246447427179213700727)
          ·
            refine ⟨51439869671140768820551091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34293246447427179213700727 51439869671140768820551091)
            ·
              refine ⟨77159804506711153230826637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51439869671140768820551091 77159804506711153230826637)
              ·
                refine ⟨28934926690016682461559989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77159804506711153230826637 28934926690016682461559989)
                ·
                  refine ⟨2712649377189063980771249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28934926690016682461559989 2712649377189063980771249)
                  ·
                    refine ⟨2034487032891797985578437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2712649377189063980771249 2034487032891797985578437)
                    ·
                      refine ⟨381466318667212122295957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2034487032891797985578437 381466318667212122295957)
                      ·
                        rfl

theorem cell23_742903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_742903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742903 prefixEnd_742903 := by exact prefixLift 742903
  have htrace : WordTrace (prefixWord ++ tailWord_742903) baseStart_742903 baseEnd_742903 := by
    simpa [prefixWord, tailWord_742903, baseEnd_742903] using wordTrace_append hprefix tailTrace_742903
  have hstable : (prefixWord ++ tailWord_742903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742903).length < 2 ^ (prefixWord ++ tailWord_742903).sum := by decide
  have hdescent : baseEnd_742903 < baseStart_742903 := by decide
  rcases family_descends (prefixWord ++ tailWord_742903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742924 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_742924 : Nat := 118140960795 + 742924 * 2 ^ 59
def prefixEnd_742924 : Nat := 4983230072969 + 3 ^ 40 * 742924 * 2
def baseEnd_742924 : Nat := 381477101760956540133361

theorem tailTrace_742924 : CollatzResearch.WordTrace tailWord_742924 prefixEnd_742924 381477101760956540133361 := by
  unfold tailWord_742924
  simp only [CollatzResearch.WordTrace]
  refine ⟨13548332180260352081385913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18064442907013802775181217 13548332180260352081385913)
  ·
    refine ⟨10161249135195264061039435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13548332180260352081385913 10161249135195264061039435)
    ·
      refine ⟨15241873702792896091559153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10161249135195264061039435 15241873702792896091559153)
      ·
        refine ⟨11431405277094672068669365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15241873702792896091559153 11431405277094672068669365)
        ·
          refine ⟨1071694244727625506437753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11431405277094672068669365 1071694244727625506437753)
          ·
            refine ⟨803770683545719129828315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1071694244727625506437753 803770683545719129828315)
            ·
              refine ⟨1205656025318578694742473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803770683545719129828315 1205656025318578694742473)
              ·
                refine ⟨904242018988934021056855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205656025318578694742473 904242018988934021056855)
                ·
                  refine ⟨1356363028483401031585283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904242018988934021056855 1356363028483401031585283)
                  ·
                    refine ⟨2034544542725101547377925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1356363028483401031585283 2034544542725101547377925)
                    ·
                      refine ⟨381477101760956540133361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2034544542725101547377925 381477101760956540133361)
                      ·
                        rfl

theorem cell23_742924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_742924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742924 prefixEnd_742924 := by exact prefixLift 742924
  have htrace : WordTrace (prefixWord ++ tailWord_742924) baseStart_742924 baseEnd_742924 := by
    simpa [prefixWord, tailWord_742924, baseEnd_742924] using wordTrace_append hprefix tailTrace_742924
  have hstable : (prefixWord ++ tailWord_742924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742924).length < 2 ^ (prefixWord ++ tailWord_742924).sum := by decide
  have hdescent : baseEnd_742924 < baseStart_742924 := by decide
  rcases family_descends (prefixWord ++ tailWord_742924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742941 : List Nat := [1, 4, 2, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_742941 : Nat := 118140960795 + 742941 * 2 ^ 59
def prefixEnd_742941 : Nat := 4983230072969 + 3 ^ 40 * 742941 * 2
def baseEnd_742941 : Nat := 381485830932082973620783

theorem tailTrace_742941 : CollatzResearch.WordTrace tailWord_742941 prefixEnd_742941 381485830932082973620783 := by
  unfold tailWord_742941
  simp only [CollatzResearch.WordTrace]
  refine ⟨27097284401459116066140677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18064856267639410710760451 27097284401459116066140677)
  ·
    refine ⟨5080740825273584262401377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27097284401459116066140677 5080740825273584262401377)
    ·
      refine ⟨3810555618955188196801033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5080740825273584262401377 3810555618955188196801033)
      ·
        refine ⟨2857916714216391147600775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3810555618955188196801033 2857916714216391147600775)
        ·
          refine ⟨4286875071324586721401163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857916714216391147600775 4286875071324586721401163)
          ·
            refine ⟨6430312606986880082101745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286875071324586721401163 6430312606986880082101745)
            ·
              refine ⟨4822734455240160061576309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6430312606986880082101745 4822734455240160061576309)
              ·
                refine ⟨452131355178765005772779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4822734455240160061576309 452131355178765005772779)
                ·
                  refine ⟨678197032768147508659169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452131355178765005772779 678197032768147508659169)
                  ·
                    refine ⟨508647774576110631494377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 678197032768147508659169 508647774576110631494377)
                    ·
                      refine ⟨381485830932082973620783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508647774576110631494377 381485830932082973620783)
                      ·
                        rfl

theorem cell23_742941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_742941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742941 prefixEnd_742941 := by exact prefixLift 742941
  have htrace : WordTrace (prefixWord ++ tailWord_742941) baseStart_742941 baseEnd_742941 := by
    simpa [prefixWord, tailWord_742941, baseEnd_742941] using wordTrace_append hprefix tailTrace_742941
  have hstable : (prefixWord ++ tailWord_742941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742941).length < 2 ^ (prefixWord ++ tailWord_742941).sum := by decide
  have hdescent : baseEnd_742941 < baseStart_742941 := by decide
  rcases family_descends (prefixWord ++ tailWord_742941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742958 : List Nat := [4, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_742958 : Nat := 118140960795 + 742958 * 2 ^ 59
def prefixEnd_742958 : Nat := 4983230072969 + 3 ^ 40 * 742958 * 2
def baseEnd_742958 : Nat := 381494560103209407108205

theorem tailTrace_742958 : CollatzResearch.WordTrace tailWord_742958 prefixEnd_742958 381494560103209407108205 := by
  unfold tailWord_742958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387238055299690996188691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18065269628265018646339685 3387238055299690996188691)
  ·
    refine ⟨5080857082949536494283037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3387238055299690996188691 5080857082949536494283037)
    ·
      refine ⟨1905321406106076185356139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5080857082949536494283037 1905321406106076185356139)
      ·
        refine ⟨2857982109159114278034209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905321406106076185356139 2857982109159114278034209)
        ·
          refine ⟨2143486581869335708525657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2857982109159114278034209 2143486581869335708525657)
          ·
            refine ⟨1607614936402001781394243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2143486581869335708525657 1607614936402001781394243)
            ·
              refine ⟨2411422404603002672091365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607614936402001781394243 2411422404603002672091365)
              ·
                refine ⟨452141700863063001017131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2411422404603002672091365 452141700863063001017131)
                ·
                  refine ⟨678212551294594501525697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452141700863063001017131 678212551294594501525697)
                  ·
                    refine ⟨508659413470945876144273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 678212551294594501525697 508659413470945876144273)
                    ·
                      refine ⟨381494560103209407108205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508659413470945876144273 381494560103209407108205)
                      ·
                        rfl

theorem cell23_742958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_742958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742958 prefixEnd_742958 := by exact prefixLift 742958
  have htrace : WordTrace (prefixWord ++ tailWord_742958) baseStart_742958 baseEnd_742958 := by
    simpa [prefixWord, tailWord_742958, baseEnd_742958] using wordTrace_append hprefix tailTrace_742958
  have hstable : (prefixWord ++ tailWord_742958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742958).length < 2 ^ (prefixWord ++ tailWord_742958).sum := by decide
  have hdescent : baseEnd_742958 < baseStart_742958 := by decide
  rcases family_descends (prefixWord ++ tailWord_742958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742967 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 3, 3, 2]
def baseStart_742967 : Nat := 118140960795 + 742967 * 2 ^ 59
def prefixEnd_742967 : Nat := 4983230072969 + 3 ^ 40 * 742967 * 2
def baseEnd_742967 : Nat := 381499181429099871895663

theorem tailTrace_742967 : CollatzResearch.WordTrace tailWord_742967 prefixEnd_742967 381499181429099871895663 := by
  unfold tailWord_742967
  simp only [CollatzResearch.WordTrace]
  refine ⟨27098232699364922506587155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18065488466243281671058103 27098232699364922506587155)
  ·
    refine ⟨40647349049047383759880733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27098232699364922506587155 40647349049047383759880733)
    ·
      refine ⟨15242755893392768909955275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40647349049047383759880733 15242755893392768909955275)
      ·
        refine ⟨22864133840089153364932913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15242755893392768909955275 22864133840089153364932913)
        ·
          refine ⟨17148100380066865023699685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22864133840089153364932913 17148100380066865023699685)
          ·
            refine ⟨3215268821262537191943691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17148100380066865023699685 3215268821262537191943691)
            ·
              refine ⟨4822903231893805787915537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215268821262537191943691 4822903231893805787915537)
              ·
                refine ⟨3617177423920354340936653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822903231893805787915537 3617177423920354340936653)
                ·
                  refine ⟨1356441533970132877851245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3617177423920354340936653 1356441533970132877851245)
                  ·
                    refine ⟨508665575238799829194217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356441533970132877851245 508665575238799829194217)
                    ·
                      refine ⟨381499181429099871895663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508665575238799829194217 381499181429099871895663)
                      ·
                        rfl

theorem cell23_742967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_742967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_742967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_742967 prefixEnd_742967 := by exact prefixLift 742967
  have htrace : WordTrace (prefixWord ++ tailWord_742967) baseStart_742967 baseEnd_742967 := by
    simpa [prefixWord, tailWord_742967, baseEnd_742967] using wordTrace_append hprefix tailTrace_742967
  have hstable : (prefixWord ++ tailWord_742967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742967).length < 2 ^ (prefixWord ++ tailWord_742967).sum := by decide
  have hdescent : baseEnd_742967 < baseStart_742967 := by decide
  rcases family_descends (prefixWord ++ tailWord_742967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743054 : List Nat := [4, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_743054 : Nat := 118140960795 + 743054 * 2 ^ 59
def prefixEnd_743054 : Nat := 4983230072969 + 3 ^ 40 * 743054 * 2
def baseEnd_743054 : Nat := 42393761582893447945307

theorem tailTrace_743054 : CollatzResearch.WordTrace tailWord_743054 prefixEnd_743054 42393761582893447945307 := by
  unfold tailWord_743054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387675731256217045625527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18067603900033157576669477 3387675731256217045625527)
  ·
    refine ⟨5081513596884325568438291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3387675731256217045625527 5081513596884325568438291)
    ·
      refine ⟨7622270395326488352657437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5081513596884325568438291 7622270395326488352657437)
      ·
        refine ⟨2858351398247433132246539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7622270395326488352657437 2858351398247433132246539)
        ·
          refine ⟨4287527097371149698369809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858351398247433132246539 4287527097371149698369809)
          ·
            refine ⟨3215645323028362273777357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4287527097371149698369809 3215645323028362273777357)
            ·
              refine ⟨1205866996135635852666509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3215645323028362273777357 1205866996135635852666509)
              ·
                refine ⟨452200123550863444749941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1205866996135635852666509 452200123550863444749941)
                ·
                  refine ⟨42393761582893447945307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 452200123550863444749941 42393761582893447945307)
                  ·
                    rfl

theorem cell23_743054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_743054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743054 prefixEnd_743054 := by exact prefixLift 743054
  have htrace : WordTrace (prefixWord ++ tailWord_743054) baseStart_743054 baseEnd_743054 := by
    simpa [prefixWord, tailWord_743054, baseEnd_743054] using wordTrace_append hprefix tailTrace_743054
  have hstable : (prefixWord ++ tailWord_743054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743054).length < 2 ^ (prefixWord ++ tailWord_743054).sum := by decide
  have hdescent : baseEnd_743054 < baseStart_743054 := by decide
  rcases family_descends (prefixWord ++ tailWord_743054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743071 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 7]
def baseStart_743071 : Nat := 118140960795 + 743071 * 2 ^ 59
def prefixEnd_743071 : Nat := 4983230072969 + 3 ^ 40 * 743071 * 2
def baseEnd_743071 : Nat := 42394731490796384999465

theorem tailTrace_743071 : CollatzResearch.WordTrace tailWord_743071 prefixEnd_743071 42394731490796384999465 := by
  unfold tailWord_743071
  simp only [CollatzResearch.WordTrace]
  refine ⟨27102025890988148268373067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18068017260658765512248711 27102025890988148268373067)
  ·
    refine ⟨40653038836482222402559601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27102025890988148268373067 40653038836482222402559601)
    ·
      refine ⟨30489779127361666801919701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40653038836482222402559601 30489779127361666801919701)
      ·
        refine ⟨714604198297539065669993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 30489779127361666801919701 714604198297539065669993)
        ·
          refine ⟨535953148723154299252495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 714604198297539065669993 535953148723154299252495)
          ·
            refine ⟨803929723084731448878743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535953148723154299252495 803929723084731448878743)
            ·
              refine ⟨1205894584627097173318115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803929723084731448878743 1205894584627097173318115)
              ·
                refine ⟨1808841876940645759977173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205894584627097173318115 1808841876940645759977173)
                ·
                  refine ⟨42394731490796384999465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1808841876940645759977173 42394731490796384999465)
                  ·
                    rfl

theorem cell23_743071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 7].length) (baseStart_743071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743071 prefixEnd_743071 := by exact prefixLift 743071
  have htrace : WordTrace (prefixWord ++ tailWord_743071) baseStart_743071 baseEnd_743071 := by
    simpa [prefixWord, tailWord_743071, baseEnd_743071] using wordTrace_append hprefix tailTrace_743071
  have hstable : (prefixWord ++ tailWord_743071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743071).length < 2 ^ (prefixWord ++ tailWord_743071).sum := by decide
  have hdescent : baseEnd_743071 < baseStart_743071 := by decide
  rcases family_descends (prefixWord ++ tailWord_743071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743087 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 1, 6, 2]
def baseStart_743087 : Nat := 118140960795 + 743087 * 2 ^ 59
def prefixEnd_743087 : Nat := 4983230072969 + 3 ^ 40 * 743087 * 2
def baseEnd_743087 : Nat := 381560799107639402395111

theorem tailTrace_743087 : CollatzResearch.WordTrace tailWord_743087 prefixEnd_743087 381560799107639402395111 := by
  unfold tailWord_743087
  simp only [CollatzResearch.WordTrace]
  refine ⟨27102609458930183000955515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18068406305953455333970343 27102609458930183000955515)
  ·
    refine ⟨40653914188395274501433273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27102609458930183000955515 40653914188395274501433273)
    ·
      refine ⟨30490435641296455876074955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40653914188395274501433273 30490435641296455876074955)
      ·
        refine ⟨45735653461944683814112433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30490435641296455876074955 45735653461944683814112433)
        ·
          refine ⟨34301740096458512860584325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45735653461944683814112433 34301740096458512860584325)
          ·
            refine ⟨6431576268085971161359561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34301740096458512860584325 6431576268085971161359561)
            ·
              refine ⟨4823682201064478371019671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6431576268085971161359561 4823682201064478371019671)
              ·
                refine ⟨7235523301596717556529507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823682201064478371019671 7235523301596717556529507)
                ·
                  refine ⟨10853284952395076334794261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7235523301596717556529507 10853284952395076334794261)
                  ·
                    refine ⟨508747732143519203193481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10853284952395076334794261 508747732143519203193481)
                    ·
                      refine ⟨381560799107639402395111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508747732143519203193481 381560799107639402395111)
                      ·
                        rfl

theorem cell23_743087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 6, 2].length) (baseStart_743087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743087 prefixEnd_743087 := by exact prefixLift 743087
  have htrace : WordTrace (prefixWord ++ tailWord_743087) baseStart_743087 baseEnd_743087 := by
    simpa [prefixWord, tailWord_743087, baseEnd_743087] using wordTrace_append hprefix tailTrace_743087
  have hstable : (prefixWord ++ tailWord_743087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743087).length < 2 ^ (prefixWord ++ tailWord_743087).sum := by decide
  have hdescent : baseEnd_743087 < baseStart_743087 := by decide
  rcases family_descends (prefixWord ++ tailWord_743087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743097 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 3, 4]
def baseStart_743097 : Nat := 118140960795 + 743097 * 2 ^ 59
def prefixEnd_743097 : Nat := 4983230072969 + 3 ^ 40 * 743097 * 2
def baseEnd_743097 : Nat := 127188644638061454423355

theorem tailTrace_743097 : CollatzResearch.WordTrace tailWord_743097 prefixEnd_743097 127188644638061454423355 := by
  unfold tailWord_743097
  simp only [CollatzResearch.WordTrace]
  refine ⟨27102974188893954708819545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18068649459262636472546363 27102974188893954708819545)
  ·
    refine ⟨20327230641670466031614659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27102974188893954708819545 20327230641670466031614659)
    ·
      refine ⟨30490845962505699047421989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20327230641670466031614659 30490845962505699047421989)
      ·
        refine ⟨5717033617969818571391623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30490845962505699047421989 5717033617969818571391623)
        ·
          refine ⟨8575550426954727857087435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5717033617969818571391623 8575550426954727857087435)
          ·
            refine ⟨12863325640432091785631153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8575550426954727857087435 12863325640432091785631153)
            ·
              refine ⟨9647494230324068839223365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12863325640432091785631153 9647494230324068839223365)
              ·
                refine ⟨1808905168185762907354381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9647494230324068839223365 1808905168185762907354381)
                ·
                  refine ⟨678339438069661090257893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1808905168185762907354381 678339438069661090257893)
                  ·
                    refine ⟨127188644638061454423355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 678339438069661090257893 127188644638061454423355)
                    ·
                      rfl

theorem cell23_743097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 4].length) (baseStart_743097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743097 prefixEnd_743097 := by exact prefixLift 743097
  have htrace : WordTrace (prefixWord ++ tailWord_743097) baseStart_743097 baseEnd_743097 := by
    simpa [prefixWord, tailWord_743097, baseEnd_743097] using wordTrace_append hprefix tailTrace_743097
  have hstable : (prefixWord ++ tailWord_743097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743097).length < 2 ^ (prefixWord ++ tailWord_743097).sum := by decide
  have hdescent : baseEnd_743097 < baseStart_743097 := by decide
  rcases family_descends (prefixWord ++ tailWord_743097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743127 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 6]
def baseStart_743127 : Nat := 118140960795 + 743127 * 2 ^ 59
def prefixEnd_743127 : Nat := 4983230072969 + 3 ^ 40 * 743127 * 2
def baseEnd_743127 : Nat := 42397926481535471766103

theorem tailTrace_743127 : CollatzResearch.WordTrace tailWord_743127 prefixEnd_743127 42397926481535471766103 := by
  unfold tailWord_743127
  simp only [CollatzResearch.WordTrace]
  refine ⟨27104068378785269832411635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18069378919190179888274423 27104068378785269832411635)
  ·
    refine ⟨40656102568177904748617453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27104068378785269832411635 40656102568177904748617453)
    ·
      refine ⟨15246038463066714280731545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40656102568177904748617453 15246038463066714280731545)
      ·
        refine ⟨11434528847300035710548659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15246038463066714280731545 11434528847300035710548659)
        ·
          refine ⟨17151793270950053565822989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11434528847300035710548659 17151793270950053565822989)
          ·
            refine ⟨6431922476606270087183621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17151793270950053565822989 6431922476606270087183621)
            ·
              refine ⟨1205985464363675641346929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6431922476606270087183621 1205985464363675641346929)
              ·
                refine ⟨904489098272756731010197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205985464363675641346929 904489098272756731010197)
                ·
                  refine ⟨42397926481535471766103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 904489098272756731010197 42397926481535471766103)
                  ·
                    rfl

theorem cell23_743127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 6].length) (baseStart_743127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743127 prefixEnd_743127 := by exact prefixLift 743127
  have htrace : WordTrace (prefixWord ++ tailWord_743127) baseStart_743127 baseEnd_743127 := by
    simpa [prefixWord, tailWord_743127, baseEnd_743127] using wordTrace_append hprefix tailTrace_743127
  have hstable : (prefixWord ++ tailWord_743127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743127).length < 2 ^ (prefixWord ++ tailWord_743127).sum := by decide
  have hdescent : baseEnd_743127 < baseStart_743127 := by decide
  rcases family_descends (prefixWord ++ tailWord_743127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743164 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_743164 : Nat := 118140960795 + 743164 * 2 ^ 59
def prefixEnd_743164 : Nat := 4983230072969 + 3 ^ 40 * 743164 * 2
def baseEnd_743164 : Nat := 381600337118035601132257

theorem tailTrace_743164 : CollatzResearch.WordTrace tailWord_743164 prefixEnd_743164 381600337118035601132257 := by
  unfold tailWord_743164
  simp only [CollatzResearch.WordTrace]
  refine ⟨13552708939825612575754273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18070278586434150101005697 13552708939825612575754273)
  ·
    refine ⟨10164531704869209431815705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13552708939825612575754273 10164531704869209431815705)
    ·
      refine ⟨7623398778651907073861779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10164531704869209431815705 7623398778651907073861779)
      ·
        refine ⟨11435098167977860610792669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7623398778651907073861779 11435098167977860610792669)
        ·
          refine ⟨4288161812991697729047251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11435098167977860610792669 4288161812991697729047251)
          ·
            refine ⟨6432242719487546593570877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288161812991697729047251 6432242719487546593570877)
            ·
              refine ⟨2412091019807829972589079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6432242719487546593570877 2412091019807829972589079)
              ·
                refine ⟨3618136529711744958883619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412091019807829972589079 3618136529711744958883619)
                ·
                  refine ⟨5427204794567617438325429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618136529711744958883619 5427204794567617438325429)
                  ·
                    refine ⟨508800449490714134843009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5427204794567617438325429 508800449490714134843009)
                    ·
                      refine ⟨381600337118035601132257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508800449490714134843009 381600337118035601132257)
                      ·
                        rfl

theorem cell23_743164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_743164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743164 prefixEnd_743164 := by exact prefixLift 743164
  have htrace : WordTrace (prefixWord ++ tailWord_743164) baseStart_743164 baseEnd_743164 := by
    simpa [prefixWord, tailWord_743164, baseEnd_743164] using wordTrace_append hprefix tailTrace_743164
  have hstable : (prefixWord ++ tailWord_743164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743164).length < 2 ^ (prefixWord ++ tailWord_743164).sum := by decide
  have hdescent : baseEnd_743164 < baseStart_743164 := by decide
  rcases family_descends (prefixWord ++ tailWord_743164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743171 : List Nat := [1, 1, 1, 3, 2, 2, 3, 5, 1, 1, 3]
def baseStart_743171 : Nat := 118140960795 + 743171 * 2 ^ 59
def prefixEnd_743171 : Nat := 4983230072969 + 3 ^ 40 * 743171 * 2
def baseEnd_743171 : Nat := 381603931482617073744725

theorem tailTrace_743171 : CollatzResearch.WordTrace tailWord_743171 prefixEnd_743171 381603931482617073744725 := by
  unfold tailWord_743171
  simp only [CollatzResearch.WordTrace]
  refine ⟨27105673190625865347013367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18070448793750576898008911 27105673190625865347013367)
  ·
    refine ⟨40658509785938798020520051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27105673190625865347013367 40658509785938798020520051)
    ·
      refine ⟨60987764678908197030780077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40658509785938798020520051 60987764678908197030780077)
      ·
        refine ⟨22870411754590573886542529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60987764678908197030780077 22870411754590573886542529)
        ·
          refine ⟨17152808815942930414906897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22870411754590573886542529 17152808815942930414906897)
          ·
            refine ⟨12864606611957197811180173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17152808815942930414906897 12864606611957197811180173)
            ·
              refine ⟨4824227479483949179192565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12864606611957197811180173 4824227479483949179192565)
              ·
                refine ⟨452271326201620235549303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4824227479483949179192565 452271326201620235549303)
                ·
                  refine ⟨678406989302430353323955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452271326201620235549303 678406989302430353323955)
                  ·
                    refine ⟨1017610483953645529985933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 678406989302430353323955 1017610483953645529985933)
                    ·
                      refine ⟨381603931482617073744725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1017610483953645529985933 381603931482617073744725)
                      ·
                        rfl

theorem cell23_743171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_743171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743171 prefixEnd_743171 := by exact prefixLift 743171
  have htrace : WordTrace (prefixWord ++ tailWord_743171) baseStart_743171 baseEnd_743171 := by
    simpa [prefixWord, tailWord_743171, baseEnd_743171] using wordTrace_append hprefix tailTrace_743171
  have hstable : (prefixWord ++ tailWord_743171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743171).length < 2 ^ (prefixWord ++ tailWord_743171).sum := by decide
  have hdescent : baseEnd_743171 < baseStart_743171 := by decide
  rcases family_descends (prefixWord ++ tailWord_743171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743204 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_743204 : Nat := 118140960795 + 743204 * 2 ^ 59
def prefixEnd_743204 : Nat := 4983230072969 + 3 ^ 40 * 743204 * 2
def baseEnd_743204 : Nat := 127206958781405148210691

theorem tailTrace_743204 : CollatzResearch.WordTrace tailWord_743204 prefixEnd_743204 127206958781405148210691 := by
  unfold tailWord_743204
  simp only [CollatzResearch.WordTrace]
  refine ⟨13553438399753155991482333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18071251199670874655309777 13553438399753155991482333)
  ·
    refine ⟨5082539399907433496805875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13553438399753155991482333 5082539399907433496805875)
    ·
      refine ⟨7623809099861150245208813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5082539399907433496805875 7623809099861150245208813)
      ·
        refine ⟨2858928412447931341953305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7623809099861150245208813 2858928412447931341953305)
        ·
          refine ⟨2144196309335948506464979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858928412447931341953305 2144196309335948506464979)
          ·
            refine ⟨3216294464003922759697469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144196309335948506464979 3216294464003922759697469)
            ·
              refine ⟨1206110424001471034886551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3216294464003922759697469 1206110424001471034886551)
              ·
                refine ⟨1809165636002206552329827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206110424001471034886551 1809165636002206552329827)
                ·
                  refine ⟨2713748454003309828494741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809165636002206552329827 2713748454003309828494741)
                  ·
                    refine ⟨127206958781405148210691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2713748454003309828494741 127206958781405148210691)
                    ·
                      rfl

theorem cell23_743204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_743204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743204 prefixEnd_743204 := by exact prefixLift 743204
  have htrace : WordTrace (prefixWord ++ tailWord_743204) baseStart_743204 baseEnd_743204 := by
    simpa [prefixWord, tailWord_743204, baseEnd_743204] using wordTrace_append hprefix tailTrace_743204
  have hstable : (prefixWord ++ tailWord_743204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743204).length < 2 ^ (prefixWord ++ tailWord_743204).sum := by decide
  have hdescent : baseEnd_743204 < baseStart_743204 := by decide
  rcases family_descends (prefixWord ++ tailWord_743204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743217 : List Nat := [1, 2, 2, 3, 2, 3, 1, 9]
def baseStart_743217 : Nat := 118140960795 + 743217 * 2 ^ 59
def prefixEnd_743217 : Nat := 4983230072969 + 3 ^ 40 * 743217 * 2
def baseEnd_743217 : Nat := 14134353762693477547019

theorem tailTrace_743217 : CollatzResearch.WordTrace tailWord_743217 prefixEnd_743217 14134353762693477547019 := by
  unfold tailWord_743217
  simp only [CollatzResearch.WordTrace]
  refine ⟨27107350948459215203187905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18071567298972810135458603 27107350948459215203187905)
  ·
    refine ⟨20330513211344411402390929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27107350948459215203187905 20330513211344411402390929)
    ·
      refine ⟨15247884908508308551793197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20330513211344411402390929 15247884908508308551793197)
      ·
        refine ⟨5717956840690615706922449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15247884908508308551793197 5717956840690615706922449)
        ·
          refine ⟨4288467630517961780191837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5717956840690615706922449 4288467630517961780191837)
          ·
            refine ⟨1608175361444235667571939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4288467630517961780191837 1608175361444235667571939)
            ·
              refine ⟨2412263042166353501357909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608175361444235667571939 2412263042166353501357909)
              ·
                refine ⟨14134353762693477547019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2412263042166353501357909 14134353762693477547019)
                ·
                  rfl

theorem cell23_743217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 9].length) (baseStart_743217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743217 prefixEnd_743217 := by exact prefixLift 743217
  have htrace : WordTrace (prefixWord ++ tailWord_743217) baseStart_743217 baseEnd_743217 := by
    simpa [prefixWord, tailWord_743217, baseEnd_743217] using wordTrace_append hprefix tailTrace_743217
  have hstable : (prefixWord ++ tailWord_743217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743217).length < 2 ^ (prefixWord ++ tailWord_743217).sum := by decide
  have hdescent : baseEnd_743217 < baseStart_743217 := by decide
  rcases family_descends (prefixWord ++ tailWord_743217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743222 : List Nat := [5, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_743222 : Nat := 118140960795 + 743222 * 2 ^ 59
def prefixEnd_743222 : Nat := 4983230072969 + 3 ^ 40 * 743222 * 2
def baseEnd_743222 : Nat := 381630118995996374206991

theorem tailTrace_743222 : CollatzResearch.WordTrace tailWord_743222 prefixEnd_743222 381630118995996374206991 := by
  unfold tailWord_743222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694220832090068816069995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18071688875627400704746613 1694220832090068816069995)
  ·
    refine ⟨2541331248135103224104993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1694220832090068816069995 2541331248135103224104993)
    ·
      refine ⟨1905998436101327418078745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2541331248135103224104993 1905998436101327418078745)
      ·
        refine ⟨1429498827075995563559059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1905998436101327418078745 1429498827075995563559059)
        ·
          refine ⟨2144248240613993345338589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429498827075995563559059 2144248240613993345338589)
          ·
            refine ⟨804093090230247504501971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2144248240613993345338589 804093090230247504501971)
            ·
              refine ⟨1206139635345371256752957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804093090230247504501971 1206139635345371256752957)
              ·
                refine ⟨452302363254514221282359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1206139635345371256752957 452302363254514221282359)
                ·
                  refine ⟨678453544881771331923539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452302363254514221282359 678453544881771331923539)
                  ·
                    refine ⟨1017680317322656997885309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 678453544881771331923539 1017680317322656997885309)
                    ·
                      refine ⟨381630118995996374206991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1017680317322656997885309 381630118995996374206991)
                      ·
                        rfl

theorem cell23_743222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_743222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743222 prefixEnd_743222 := by exact prefixLift 743222
  have htrace : WordTrace (prefixWord ++ tailWord_743222) baseStart_743222 baseEnd_743222 := by
    simpa [prefixWord, tailWord_743222, baseEnd_743222] using wordTrace_append hprefix tailTrace_743222
  have hstable : (prefixWord ++ tailWord_743222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743222).length < 2 ^ (prefixWord ++ tailWord_743222).sum := by decide
  have hdescent : baseEnd_743222 < baseStart_743222 := by decide
  rcases family_descends (prefixWord ++ tailWord_743222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743238 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_743238 : Nat := 118140960795 + 743238 * 2 ^ 59
def prefixEnd_743238 : Nat := 4983230072969 + 3 ^ 40 * 743238 * 2
def baseEnd_743238 : Nat := 127212778228822770535639

theorem tailTrace_743238 : CollatzResearch.WordTrace tailWord_743238 prefixEnd_743238 127212778228822770535639 := by
  unfold tailWord_743238
  simp only [CollatzResearch.WordTrace]
  refine ⟨847128652543222993428199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18072077920922090526468245 847128652543222993428199)
  ·
    refine ⟨1270692978814834490142299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 847128652543222993428199 1270692978814834490142299)
    ·
      refine ⟨1906039468222251735213449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270692978814834490142299 1906039468222251735213449)
      ·
        refine ⟨1429529601166688801410087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1906039468222251735213449 1429529601166688801410087)
        ·
          refine ⟨2144294401750033202115131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429529601166688801410087 2144294401750033202115131)
          ·
            refine ⟨3216441602625049803172697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144294401750033202115131 3216441602625049803172697)
            ·
              refine ⟨2412331201968787352379523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216441602625049803172697 2412331201968787352379523)
              ·
                refine ⟨3618496802953181028569285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412331201968787352379523 3618496802953181028569285)
                ·
                  refine ⟨678468150553721442856741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3618496802953181028569285 678468150553721442856741)
                  ·
                    refine ⟨127212778228822770535639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 678468150553721442856741 127212778228822770535639)
                    ·
                      rfl

theorem cell23_743238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_743238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743238 prefixEnd_743238 := by exact prefixLift 743238
  have htrace : WordTrace (prefixWord ++ tailWord_743238) baseStart_743238 baseEnd_743238 := by
    simpa [prefixWord, tailWord_743238, baseEnd_743238] using wordTrace_append hprefix tailTrace_743238
  have hstable : (prefixWord ++ tailWord_743238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743238).length < 2 ^ (prefixWord ++ tailWord_743238).sum := by decide
  have hdescent : baseEnd_743238 < baseStart_743238 := by decide
  rcases family_descends (prefixWord ++ tailWord_743238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743245 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_743245 : Nat := 118140960795 + 743245 * 2 ^ 59
def prefixEnd_743245 : Nat := 4983230072969 + 3 ^ 40 * 743245 * 2
def baseEnd_743245 : Nat := 381641929051049784219385

theorem tailTrace_743245 : CollatzResearch.WordTrace tailWord_743245 prefixEnd_743245 381641929051049784219385 := by
  unfold tailWord_743245
  simp only [CollatzResearch.WordTrace]
  refine ⟨27108372192357775985207189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18072248128238517323471459 27108372192357775985207189)
  ·
    refine ⟨1270704946516770749306587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27108372192357775985207189 1270704946516770749306587)
    ·
      refine ⟨1906057419775156123959881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270704946516770749306587 1906057419775156123959881)
      ·
        refine ⟨1429543064831367092969911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1906057419775156123959881 1429543064831367092969911)
        ·
          refine ⟨2144314597247050639454867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429543064831367092969911 2144314597247050639454867)
          ·
            refine ⟨3216471895870575959182301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144314597247050639454867 3216471895870575959182301)
            ·
              refine ⟨1206176960951465984693363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3216471895870575959182301 1206176960951465984693363)
              ·
                refine ⟨1809265441427198977040045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206176960951465984693363 1809265441427198977040045)
                ·
                  refine ⟨678474540535199616390017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1809265441427198977040045 678474540535199616390017)
                  ·
                    refine ⟨508855905401399712292513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 678474540535199616390017 508855905401399712292513)
                    ·
                      refine ⟨381641929051049784219385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508855905401399712292513 381641929051049784219385)
                      ·
                        rfl

theorem cell23_743245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_743245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743245 prefixEnd_743245 := by exact prefixLift 743245
  have htrace : WordTrace (prefixWord ++ tailWord_743245) baseStart_743245 baseEnd_743245 := by
    simpa [prefixWord, tailWord_743245, baseEnd_743245] using wordTrace_append hprefix tailTrace_743245
  have hstable : (prefixWord ++ tailWord_743245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743245).length < 2 ^ (prefixWord ++ tailWord_743245).sum := by decide
  have hdescent : baseEnd_743245 < baseStart_743245 := by decide
  rcases family_descends (prefixWord ++ tailWord_743245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743255 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 2, 4]
def baseStart_743255 : Nat := 118140960795 + 743255 * 2 ^ 59
def prefixEnd_743255 : Nat := 4983230072969 + 3 ^ 40 * 743255 * 2
def baseEnd_743255 : Nat := 127215687952531581698113

theorem tailTrace_743255 : CollatzResearch.WordTrace tailWord_743255 prefixEnd_743255 127215687952531581698113 := by
  unfold tailWord_743255
  simp only [CollatzResearch.WordTrace]
  refine ⟨27108736922321547693071219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18072491281547698462047479 27108736922321547693071219)
  ·
    refine ⟨40663105383482321539606829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27108736922321547693071219 40663105383482321539606829)
    ·
      refine ⟨15248664518805870577352561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40663105383482321539606829 15248664518805870577352561)
      ·
        refine ⟨11436498389104402933014421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15248664518805870577352561 11436498389104402933014421)
        ·
          refine ⟨536085861989268887485051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11436498389104402933014421 536085861989268887485051)
          ·
            refine ⟨804128792983903331227577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536085861989268887485051 804128792983903331227577)
            ·
              refine ⟨603096594737927498420683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804128792983903331227577 603096594737927498420683)
              ·
                refine ⟨904644892106891247631025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603096594737927498420683 904644892106891247631025)
                ·
                  refine ⟨678483669080168435723269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 904644892106891247631025 678483669080168435723269)
                  ·
                    refine ⟨127215687952531581698113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 678483669080168435723269 127215687952531581698113)
                    ·
                      rfl

theorem cell23_743255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_743255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743255 prefixEnd_743255 := by exact prefixLift 743255
  have htrace : WordTrace (prefixWord ++ tailWord_743255) baseStart_743255 baseEnd_743255 := by
    simpa [prefixWord, tailWord_743255, baseEnd_743255] using wordTrace_append hprefix tailTrace_743255
  have hstable : (prefixWord ++ tailWord_743255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743255).length < 2 ^ (prefixWord ++ tailWord_743255).sum := by decide
  have hdescent : baseEnd_743255 < baseStart_743255 := by decide
  rcases family_descends (prefixWord ++ tailWord_743255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743271 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_743271 : Nat := 118140960795 + 743271 * 2 ^ 59
def prefixEnd_743271 : Nat := 4983230072969 + 3 ^ 40 * 743271 * 2
def baseEnd_743271 : Nat := 381655279548066682494265

theorem tailTrace_743271 : CollatzResearch.WordTrace tailWord_743271 prefixEnd_743271 381655279548066682494265 := by
  unfold tailWord_743271
  simp only [CollatzResearch.WordTrace]
  refine ⟨27109320490263582425653667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18072880326842388283769111 27109320490263582425653667)
  ·
    refine ⟨40663980735395373638480501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27109320490263582425653667 40663980735395373638480501)
    ·
      refine ⟨3812248193943316278607547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40663980735395373638480501 3812248193943316278607547)
      ·
        refine ⟨5718372290914974417911321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812248193943316278607547 5718372290914974417911321)
        ·
          refine ⟨4288779218186230813433491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5718372290914974417911321 4288779218186230813433491)
          ·
            refine ⟨6433168827279346220150237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288779218186230813433491 6433168827279346220150237)
            ·
              refine ⟨2412438310229754832556339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6433168827279346220150237 2412438310229754832556339)
              ·
                refine ⟨3618657465344632248834509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412438310229754832556339 3618657465344632248834509)
                ·
                  refine ⟨1356996549504237093312941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3618657465344632248834509 1356996549504237093312941)
                  ·
                    refine ⟨508873706064088909992353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356996549504237093312941 508873706064088909992353)
                    ·
                      refine ⟨381655279548066682494265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 508873706064088909992353 381655279548066682494265)
                      ·
                        rfl

theorem cell23_743271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_743271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743271 prefixEnd_743271 := by exact prefixLift 743271
  have htrace : WordTrace (prefixWord ++ tailWord_743271) baseStart_743271 baseEnd_743271 := by
    simpa [prefixWord, tailWord_743271, baseEnd_743271] using wordTrace_append hprefix tailTrace_743271
  have hstable : (prefixWord ++ tailWord_743271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743271).length < 2 ^ (prefixWord ++ tailWord_743271).sum := by decide
  have hdescent : baseEnd_743271 < baseStart_743271 := by decide
  rcases family_descends (prefixWord ++ tailWord_743271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743307 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 7]
def baseStart_743307 : Nat := 118140960795 + 743307 * 2 ^ 59
def prefixEnd_743307 : Nat := 4983230072969 + 3 ^ 40 * 743307 * 2
def baseEnd_743307 : Nat := 42408196094625393516011

theorem tailTrace_743307 : CollatzResearch.WordTrace tailWord_743307 prefixEnd_743307 42408196094625393516011 := by
  unfold tailWord_743307
  simp only [CollatzResearch.WordTrace]
  refine ⟨27110633518133160573964175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18073755678755440382642783 27110633518133160573964175)
  ·
    refine ⟨40665950277199740860946263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27110633518133160573964175 40665950277199740860946263)
    ·
      refine ⟨60998925415799611291419395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40665950277199740860946263 60998925415799611291419395)
      ·
        refine ⟨91498388123699416937129093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60998925415799611291419395 91498388123699416937129093)
        ·
          refine ⟨17155947773193640675711705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91498388123699416937129093 17155947773193640675711705)
          ·
            refine ⟨12866960829895230506783779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17155947773193640675711705 12866960829895230506783779)
            ·
              refine ⟨19300441244842845760175669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12866960829895230506783779 19300441244842845760175669)
              ·
                refine ⟨1809416366704016790016469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19300441244842845760175669 1809416366704016790016469)
                ·
                  refine ⟨42408196094625393516011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1809416366704016790016469 42408196094625393516011)
                  ·
                    rfl

theorem cell23_743307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 7].length) (baseStart_743307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743307 prefixEnd_743307 := by exact prefixLift 743307
  have htrace : WordTrace (prefixWord ++ tailWord_743307) baseStart_743307 baseEnd_743307 := by
    simpa [prefixWord, tailWord_743307, baseEnd_743307] using wordTrace_append hprefix tailTrace_743307
  have hstable : (prefixWord ++ tailWord_743307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743307).length < 2 ^ (prefixWord ++ tailWord_743307).sum := by decide
  have hdescent : baseEnd_743307 < baseStart_743307 := by decide
  rcases family_descends (prefixWord ++ tailWord_743307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743324 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 9]
def baseStart_743324 : Nat := 118140960795 + 743324 * 2 ^ 59
def prefixEnd_743324 : Nat := 4983230072969 + 3 ^ 40 * 743324 * 2
def baseEnd_743324 : Nat := 42409166002528330570169

theorem tailTrace_743324 : CollatzResearch.WordTrace tailWord_743324 prefixEnd_743324 42409166002528330570169 := by
  unfold tailWord_743324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13555626779535786238666513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18074169039381048318222017 13555626779535786238666513)
  ·
    refine ⟨10166720084651839678999885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13555626779535786238666513 10166720084651839678999885)
    ·
      refine ⟨3812520031744439879624957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10166720084651839678999885 3812520031744439879624957)
      ·
        refine ⟨1429695011904164954859359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3812520031744439879624957 1429695011904164954859359)
        ·
          refine ⟨2144542517856247432289039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429695011904164954859359 2144542517856247432289039)
          ·
            refine ⟨3216813776784371148433559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144542517856247432289039 3216813776784371148433559)
            ·
              refine ⟨4825220665176556722650339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216813776784371148433559 4825220665176556722650339)
              ·
                refine ⟨7237830997764835083975509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825220665176556722650339 7237830997764835083975509)
                ·
                  refine ⟨42409166002528330570169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7237830997764835083975509 42409166002528330570169)
                  ·
                    rfl

theorem cell23_743324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_743324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743324 prefixEnd_743324 := by exact prefixLift 743324
  have htrace : WordTrace (prefixWord ++ tailWord_743324) baseStart_743324 baseEnd_743324 := by
    simpa [prefixWord, tailWord_743324, baseEnd_743324] using wordTrace_append hprefix tailTrace_743324
  have hstable : (prefixWord ++ tailWord_743324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743324).length < 2 ^ (prefixWord ++ tailWord_743324).sum := by decide
  have hdescent : baseEnd_743324 < baseStart_743324 := by decide
  rcases family_descends (prefixWord ++ tailWord_743324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743374 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_743374 : Nat := 118140960795 + 743374 * 2 ^ 59
def prefixEnd_743374 : Nat := 4983230072969 + 3 ^ 40 * 743374 * 2
def baseEnd_743374 : Nat := 381708168055479779506291

theorem tailTrace_743374 : CollatzResearch.WordTrace tailWord_743374 prefixEnd_743374 381708168055479779506291 := by
  unfold tailWord_743374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389134651111303877081647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18075384805926954011102117 3389134651111303877081647)
  ·
    refine ⟨5083701976666955815622471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3389134651111303877081647 5083701976666955815622471)
    ·
      refine ⟨7625552965000433723433707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5083701976666955815622471 7625552965000433723433707)
      ·
        refine ⟨11438329447500650585150561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7625552965000433723433707 11438329447500650585150561)
        ·
          refine ⟨8578747085625487938862921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11438329447500650585150561 8578747085625487938862921)
          ·
            refine ⟨6434060314219115954147191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8578747085625487938862921 6434060314219115954147191)
            ·
              refine ⟨9651090471328673931220787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434060314219115954147191 9651090471328673931220787)
              ·
                refine ⟨14476635706993010896831181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9651090471328673931220787 14476635706993010896831181)
                ·
                  refine ⟨5428738390122379086311693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14476635706993010896831181 5428738390122379086311693)
                  ·
                    refine ⟨2035776896295892157366885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5428738390122379086311693 2035776896295892157366885)
                    ·
                      refine ⟨381708168055479779506291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2035776896295892157366885 381708168055479779506291)
                      ·
                        rfl

theorem cell23_743374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_743374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743374 prefixEnd_743374 := by exact prefixLift 743374
  have htrace : WordTrace (prefixWord ++ tailWord_743374) baseStart_743374 baseEnd_743374 := by
    simpa [prefixWord, tailWord_743374, baseEnd_743374] using wordTrace_append hprefix tailTrace_743374
  have hstable : (prefixWord ++ tailWord_743374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743374).length < 2 ^ (prefixWord ++ tailWord_743374).sum := by decide
  have hdescent : baseEnd_743374 < baseStart_743374 := by decide
  rcases family_descends (prefixWord ++ tailWord_743374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743424 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 3]
def baseStart_743424 : Nat := 118140960795 + 743424 * 2 ^ 59
def prefixEnd_743424 : Nat := 4983230072969 + 3 ^ 40 * 743424 * 2
def baseEnd_743424 : Nat := 381733842088204583881061

theorem tailTrace_743424 : CollatzResearch.WordTrace tailWord_743424 prefixEnd_743424 381733842088204583881061 := by
  unfold tailWord_743424
  simp only [CollatzResearch.WordTrace]
  refine ⟨13557450429354644777986663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18076600572472859703982217 13557450429354644777986663)
  ·
    refine ⟨20336175644031967166979995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13557450429354644777986663 20336175644031967166979995)
    ·
      refine ⟨30504263466047950750469993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20336175644031967166979995 30504263466047950750469993)
      ·
        refine ⟨22878197599535963062852495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30504263466047950750469993 22878197599535963062852495)
        ·
          refine ⟨34317296399303944594278743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22878197599535963062852495 34317296399303944594278743)
          ·
            refine ⟨51475944598955916891418115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34317296399303944594278743 51475944598955916891418115)
            ·
              refine ⟨77213916898433875337127173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51475944598955916891418115 77213916898433875337127173)
              ·
                refine ⟨14477609418456351625711345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77213916898433875337127173 14477609418456351625711345)
                ·
                  refine ⟨10858207063842263719283509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14477609418456351625711345 10858207063842263719283509)
                  ·
                    refine ⟨1017956912235212223682829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10858207063842263719283509 1017956912235212223682829)
                    ·
                      refine ⟨381733842088204583881061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1017956912235212223682829 381733842088204583881061)
                      ·
                        rfl

theorem cell23_743424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_743424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743424 prefixEnd_743424 := by exact prefixLift 743424
  have htrace : WordTrace (prefixWord ++ tailWord_743424) baseStart_743424 baseEnd_743424 := by
    simpa [prefixWord, tailWord_743424, baseEnd_743424] using wordTrace_append hprefix tailTrace_743424
  have hstable : (prefixWord ++ tailWord_743424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743424).length < 2 ^ (prefixWord ++ tailWord_743424).sum := by decide
  have hdescent : baseEnd_743424 < baseStart_743424 := by decide
  rcases family_descends (prefixWord ++ tailWord_743424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743431 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 6]
def baseStart_743431 : Nat := 118140960795 + 743431 * 2 ^ 59
def prefixEnd_743431 : Nat := 4983230072969 + 3 ^ 40 * 743431 * 2
def baseEnd_743431 : Nat := 42415270716976228499281

theorem tailTrace_743431 : CollatzResearch.WordTrace tailWord_743431 prefixEnd_743431 42415270716976228499281 := by
  unfold tailWord_743431
  simp only [CollatzResearch.WordTrace]
  refine ⟨27115156169683929751478147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18076770779789286500985431 27115156169683929751478147)
  ·
    refine ⟨40672734254525894627217221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27115156169683929751478147 40672734254525894627217221)
    ·
      refine ⟨7626137672723605242603229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40672734254525894627217221 7626137672723605242603229)
      ·
        refine ⟨2859801627271351965976211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7626137672723605242603229 2859801627271351965976211)
        ·
          refine ⟨4289702440907027948964317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859801627271351965976211 4289702440907027948964317)
          ·
            refine ⟨1608638415340135480861619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4289702440907027948964317 1608638415340135480861619)
            ·
              refine ⟨2412957623010203221292429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608638415340135480861619 2412957623010203221292429)
              ·
                refine ⟨904859108628826207984661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2412957623010203221292429 904859108628826207984661)
                ·
                  refine ⟨42415270716976228499281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 904859108628826207984661 42415270716976228499281)
                  ·
                    rfl

theorem cell23_743431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 6].length) (baseStart_743431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743431 prefixEnd_743431 := by exact prefixLift 743431
  have htrace : WordTrace (prefixWord ++ tailWord_743431) baseStart_743431 baseEnd_743431 := by
    simpa [prefixWord, tailWord_743431, baseEnd_743431] using wordTrace_append hprefix tailTrace_743431
  have hstable : (prefixWord ++ tailWord_743431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743431).length < 2 ^ (prefixWord ++ tailWord_743431).sum := by decide
  have hdescent : baseEnd_743431 < baseStart_743431 := by decide
  rcases family_descends (prefixWord ++ tailWord_743431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743511 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_743511 : Nat := 118140960795 + 743511 * 2 ^ 59
def prefixEnd_743511 : Nat := 4983230072969 + 3 ^ 40 * 743511 * 2
def baseEnd_743511 : Nat := 381778514905145743493161

theorem tailTrace_743511 : CollatzResearch.WordTrace tailWord_743511 prefixEnd_743511 381778514905145743493161 := by
  unfold tailWord_743511
  simp only [CollatzResearch.WordTrace]
  refine ⟨27118074009394103414390387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18078716006262735609593591 27118074009394103414390387)
  ·
    refine ⟨40677111014091155121585581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27118074009394103414390387 40677111014091155121585581)
    ·
      refine ⟨15253916630284183170594593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40677111014091155121585581 15253916630284183170594593)
      ·
        refine ⟨11440437472713137377945945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15253916630284183170594593 11440437472713137377945945)
        ·
          refine ⟨8580328104534853033459459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11440437472713137377945945 8580328104534853033459459)
          ·
            refine ⟨12870492156802279550189189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8580328104534853033459459 12870492156802279550189189)
            ·
              refine ⟨2413217279400427415660473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12870492156802279550189189 2413217279400427415660473)
              ·
                refine ⟨1809912959550320561745355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2413217279400427415660473 1809912959550320561745355)
                ·
                  refine ⟨2714869439325480842618033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809912959550320561745355 2714869439325480842618033)
                  ·
                    refine ⟨2036152079494110631963525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2714869439325480842618033 2036152079494110631963525)
                    ·
                      refine ⟨381778514905145743493161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2036152079494110631963525 381778514905145743493161)
                      ·
                        rfl

theorem cell23_743511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_743511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743511 prefixEnd_743511 := by exact prefixLift 743511
  have htrace : WordTrace (prefixWord ++ tailWord_743511) baseStart_743511 baseEnd_743511 := by
    simpa [prefixWord, tailWord_743511, baseEnd_743511] using wordTrace_append hprefix tailTrace_743511
  have hstable : (prefixWord ++ tailWord_743511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743511).length < 2 ^ (prefixWord ++ tailWord_743511).sum := by decide
  have hdescent : baseEnd_743511 < baseStart_743511 := by decide
  rcases family_descends (prefixWord ++ tailWord_743511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743525 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_743525 : Nat := 118140960795 + 743525 * 2 ^ 59
def prefixEnd_743525 : Nat := 4983230072969 + 3 ^ 40 * 743525 * 2
def baseEnd_743525 : Nat := 127261901211436229572699

theorem tailTrace_743525 : CollatzResearch.WordTrace tailWord_743525 prefixEnd_743525 127261901211436229572699 := by
  unfold tailWord_743525
  simp only [CollatzResearch.WordTrace]
  refine ⟨27118584631343383805400029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18079056420895589203600019 27118584631343383805400029)
  ·
    refine ⟨10169469236753768927025011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27118584631343383805400029 10169469236753768927025011)
    ·
      refine ⟨15254203855130653390537517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169469236753768927025011 15254203855130653390537517)
      ·
        refine ⟨5720326445673995021451569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15254203855130653390537517 5720326445673995021451569)
        ·
          refine ⟨4290244834255496266088677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5720326445673995021451569 4290244834255496266088677)
          ·
            refine ⟨804420906422905549891627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4290244834255496266088677 804420906422905549891627)
            ·
              refine ⟨1206631359634358324837441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804420906422905549891627 1206631359634358324837441)
              ·
                refine ⟨904973519725768743628081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206631359634358324837441 904973519725768743628081)
                ·
                  refine ⟨678730139794326557721061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 904973519725768743628081 678730139794326557721061)
                  ·
                    refine ⟨127261901211436229572699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 678730139794326557721061 127261901211436229572699)
                    ·
                      rfl

theorem cell23_743525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_743525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743525 prefixEnd_743525 := by exact prefixLift 743525
  have htrace : WordTrace (prefixWord ++ tailWord_743525) baseStart_743525 baseEnd_743525 := by
    simpa [prefixWord, tailWord_743525, baseEnd_743525] using wordTrace_append hprefix tailTrace_743525
  have hstable : (prefixWord ++ tailWord_743525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743525).length < 2 ^ (prefixWord ++ tailWord_743525).sum := by decide
  have hdescent : baseEnd_743525 < baseStart_743525 := by decide
  rcases family_descends (prefixWord ++ tailWord_743525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743532 : List Nat := [2, 2, 1, 1, 3, 3, 2, 4, 1, 2, 2]
def baseStart_743532 : Nat := 118140960795 + 743532 * 2 ^ 59
def prefixEnd_743532 : Nat := 4983230072969 + 3 ^ 40 * 743532 * 2
def baseEnd_743532 : Nat := 381789297998890161330565

theorem tailTrace_743532 : CollatzResearch.WordTrace tailWord_743532 prefixEnd_743532 381789297998890161330565 := by
  unfold tailWord_743532
  simp only [CollatzResearch.WordTrace]
  refine ⟨13559419971159012000452425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18079226628212016000603233 13559419971159012000452425)
  ·
    refine ⟨10169564978369259000339319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13559419971159012000452425 10169564978369259000339319)
    ·
      refine ⟨15254347467553888500508979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169564978369259000339319 15254347467553888500508979)
      ·
        refine ⟨22881521201330832750763469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15254347467553888500508979 22881521201330832750763469)
        ·
          refine ⟨8580570450499062281536301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22881521201330832750763469 8580570450499062281536301)
          ·
            refine ⟨3217713918937148355576113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8580570450499062281536301 3217713918937148355576113)
            ·
              refine ⟨2413285439202861266682085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3217713918937148355576113 2413285439202861266682085)
              ·
                refine ⟨452491019850536487502891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2413285439202861266682085 452491019850536487502891)
                ·
                  refine ⟨678736529775804731254337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452491019850536487502891 678736529775804731254337)
                  ·
                    refine ⟨509052397331853548440753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 678736529775804731254337 509052397331853548440753)
                    ·
                      refine ⟨381789297998890161330565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509052397331853548440753 381789297998890161330565)
                      ·
                        rfl

theorem cell23_743532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_743532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743532 prefixEnd_743532 := by exact prefixLift 743532
  have htrace : WordTrace (prefixWord ++ tailWord_743532) baseStart_743532 baseEnd_743532 := by
    simpa [prefixWord, tailWord_743532, baseEnd_743532] using wordTrace_append hprefix tailTrace_743532
  have hstable : (prefixWord ++ tailWord_743532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743532).length < 2 ^ (prefixWord ++ tailWord_743532).sum := by decide
  have hdescent : baseEnd_743532 < baseStart_743532 := by decide
  rcases family_descends (prefixWord ++ tailWord_743532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743542 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_743542 : Nat := 118140960795 + 743542 * 2 ^ 59
def prefixEnd_743542 : Nat := 4983230072969 + 3 ^ 40 * 743542 * 2
def baseEnd_743542 : Nat := 127264810935145040735173

theorem tailTrace_743542 : CollatzResearch.WordTrace tailWord_743542 prefixEnd_743542 127264810935145040735173 := by
  unfold tailWord_743542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694950292017612231798055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18079469781521197139179253 1694950292017612231798055)
  ·
    refine ⟨2542425438026418347697083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1694950292017612231798055 2542425438026418347697083)
    ·
      refine ⟨3813638157039627521545625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542425438026418347697083 3813638157039627521545625)
      ·
        refine ⟨2860228617779720641159219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3813638157039627521545625 2860228617779720641159219)
        ·
          refine ⟨4290342926669580961738829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860228617779720641159219 4290342926669580961738829)
          ·
            refine ⟨1608878597501092860652061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4290342926669580961738829 1608878597501092860652061)
            ·
              refine ⟨603329474062909822744523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1608878597501092860652061 603329474062909822744523)
              ·
                refine ⟨904994211094364734116785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603329474062909822744523 904994211094364734116785)
                ·
                  refine ⟨678745658320773550587589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 904994211094364734116785 678745658320773550587589)
                  ·
                    refine ⟨127264810935145040735173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 678745658320773550587589 127264810935145040735173)
                    ·
                      rfl

theorem cell23_743542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_743542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743542 prefixEnd_743542 := by exact prefixLift 743542
  have htrace : WordTrace (prefixWord ++ tailWord_743542) baseStart_743542 baseEnd_743542 := by
    simpa [prefixWord, tailWord_743542, baseEnd_743542] using wordTrace_append hprefix tailTrace_743542
  have hstable : (prefixWord ++ tailWord_743542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743542).length < 2 ^ (prefixWord ++ tailWord_743542).sum := by decide
  have hdescent : baseEnd_743542 < baseStart_743542 := by decide
  rcases family_descends (prefixWord ++ tailWord_743542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743548 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_743548 : Nat := 118140960795 + 743548 * 2 ^ 59
def prefixEnd_743548 : Nat := 4983230072969 + 3 ^ 40 * 743548 * 2
def baseEnd_743548 : Nat := 381797513689362098730491

theorem tailTrace_743548 : CollatzResearch.WordTrace tailWord_743548 prefixEnd_743548 381797513689362098730491 := by
  unfold tailWord_743548
  simp only [CollatzResearch.WordTrace]
  refine ⟨13559711755130029366743649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18079615673506705822324865 13559711755130029366743649)
  ·
    refine ⟨10169783816347522025057737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13559711755130029366743649 10169783816347522025057737)
    ·
      refine ⟨7627337862260641518793303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10169783816347522025057737 7627337862260641518793303)
      ·
        refine ⟨11441006793390962278189955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7627337862260641518793303 11441006793390962278189955)
        ·
          refine ⟨17161510190086443417284933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11441006793390962278189955 17161510190086443417284933)
          ·
            refine ⟨3217783160641208140740925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17161510190086443417284933 3217783160641208140740925)
            ·
              refine ⟨1206668685240453052777847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3217783160641208140740925 1206668685240453052777847)
              ·
                refine ⟨1810003027860679579166771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206668685240453052777847 1810003027860679579166771)
                ·
                  refine ⟨2715004541791019368750157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810003027860679579166771 2715004541791019368750157)
                  ·
                    refine ⟨1018126703171632263281309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715004541791019368750157 1018126703171632263281309)
                    ·
                      refine ⟨381797513689362098730491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1018126703171632263281309 381797513689362098730491)
                      ·
                        rfl

theorem cell23_743548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_743548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743548 prefixEnd_743548 := by exact prefixLift 743548
  have htrace : WordTrace (prefixWord ++ tailWord_743548) baseStart_743548 baseEnd_743548 := by
    simpa [prefixWord, tailWord_743548, baseEnd_743548] using wordTrace_append hprefix tailTrace_743548
  have hstable : (prefixWord ++ tailWord_743548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743548).length < 2 ^ (prefixWord ++ tailWord_743548).sum := by decide
  have hdescent : baseEnd_743548 < baseStart_743548 := by decide
  rcases family_descends (prefixWord ++ tailWord_743548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743566 : List Nat := [4, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_743566 : Nat := 118140960795 + 743566 * 2 ^ 59
def prefixEnd_743566 : Nat := 4983230072969 + 3 ^ 40 * 743566 * 2
def baseEnd_743566 : Nat := 381806756341143028305409

theorem tailTrace_743566 : CollatzResearch.WordTrace tailWord_743566 prefixEnd_743566 381806756341143028305409 := by
  unfold tailWord_743566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390010003024355975955319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18080053349463231871761701 3390010003024355975955319)
  ·
    refine ⟨5085015004536533963932979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3390010003024355975955319 5085015004536533963932979)
    ·
      refine ⟨7627522506804800945899469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5085015004536533963932979 7627522506804800945899469)
      ·
        refine ⟨2860320940051800354712301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7627522506804800945899469 2860320940051800354712301)
        ·
          refine ⟨1072620352519425133017113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2860320940051800354712301 1072620352519425133017113)
          ·
            refine ⟨804465264389568849762835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072620352519425133017113 804465264389568849762835)
            ·
              refine ⟨1206697896584353274644253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804465264389568849762835 1206697896584353274644253)
              ·
                refine ⟨452511711219132477991595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1206697896584353274644253 452511711219132477991595)
                ·
                  refine ⟨678767566828698716987393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452511711219132477991595 678767566828698716987393)
                  ·
                    refine ⟨509075675121524037740545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 678767566828698716987393 509075675121524037740545)
                    ·
                      refine ⟨381806756341143028305409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509075675121524037740545 381806756341143028305409)
                      ·
                        rfl

theorem cell23_743566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_743566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743566 prefixEnd_743566 := by exact prefixLift 743566
  have htrace : WordTrace (prefixWord ++ tailWord_743566) baseStart_743566 baseEnd_743566 := by
    simpa [prefixWord, tailWord_743566, baseEnd_743566] using wordTrace_append hprefix tailTrace_743566
  have hstable : (prefixWord ++ tailWord_743566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743566).length < 2 ^ (prefixWord ++ tailWord_743566).sum := by decide
  have hdescent : baseEnd_743566 < baseStart_743566 := by decide
  rcases family_descends (prefixWord ++ tailWord_743566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743648 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 1, 7, 2]
def baseStart_743648 : Nat := 118140960795 + 743648 * 2 ^ 59
def prefixEnd_743648 : Nat := 4983230072969 + 3 ^ 40 * 743648 * 2
def baseEnd_743648 : Nat := 381848861754811707480031

theorem tailTrace_743648 : CollatzResearch.WordTrace tailWord_743648 prefixEnd_743648 381848861754811707480031 := by
  unfold tailWord_743648
  simp only [CollatzResearch.WordTrace]
  refine ⟨13561535404948887906063799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18082047206598517208085065 13561535404948887906063799)
  ·
    refine ⟨20342303107423331859095699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13561535404948887906063799 20342303107423331859095699)
    ·
      refine ⟨30513454661134997788643549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20342303107423331859095699 30513454661134997788643549)
      ·
        refine ⟨11442545497925624170741331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30513454661134997788643549 11442545497925624170741331)
        ·
          refine ⟨17163818246888436256111997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11442545497925624170741331 17163818246888436256111997)
          ·
            refine ⟨6436431842583163596041999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17163818246888436256111997 6436431842583163596041999)
            ·
              refine ⟨9654647763874745394062999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6436431842583163596041999 9654647763874745394062999)
              ·
                refine ⟨14481971645812118091094499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9654647763874745394062999 14481971645812118091094499)
                ·
                  refine ⟨21722957468718177136641749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14481971645812118091094499 21722957468718177136641749)
                  ·
                    refine ⟨509131815673082276640041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21722957468718177136641749 509131815673082276640041)
                    ·
                      refine ⟨381848861754811707480031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509131815673082276640041 381848861754811707480031)
                      ·
                        rfl

theorem cell23_743648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_743648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743648 prefixEnd_743648 := by exact prefixLift 743648
  have htrace : WordTrace (prefixWord ++ tailWord_743648) baseStart_743648 baseEnd_743648 := by
    simpa [prefixWord, tailWord_743648, baseEnd_743648] using wordTrace_append hprefix tailTrace_743648
  have hstable : (prefixWord ++ tailWord_743648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743648).length < 2 ^ (prefixWord ++ tailWord_743648).sum := by decide
  have hdescent : baseEnd_743648 < baseStart_743648 := by decide
  rcases family_descends (prefixWord ++ tailWord_743648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743655 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_743655 : Nat := 118140960795 + 743655 * 2 ^ 59
def prefixEnd_743655 : Nat := 4983230072969 + 3 ^ 40 * 743655 * 2
def baseEnd_743655 : Nat := 381852456119393180092499

theorem tailTrace_743655 : CollatzResearch.WordTrace tailWord_743655 prefixEnd_743655 381852456119393180092499 := by
  unfold tailWord_743655
  simp only [CollatzResearch.WordTrace]
  refine ⟨27123326120872416007632419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18082217413914944005088279 27123326120872416007632419)
  ·
    refine ⟨40684989181308624011448629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27123326120872416007632419 40684989181308624011448629)
    ·
      refine ⟨3814217735747683501073309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40684989181308624011448629 3814217735747683501073309)
      ·
        refine ⟨1430331650905381312902491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3814217735747683501073309 1430331650905381312902491)
        ·
          refine ⟨2145497476358071969353737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430331650905381312902491 2145497476358071969353737)
          ·
            refine ⟨1609123107268553977015303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145497476358071969353737 1609123107268553977015303)
            ·
              refine ⟨2413684660902830965522955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609123107268553977015303 2413684660902830965522955)
              ·
                refine ⟨3620526991354246448284433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413684660902830965522955 3620526991354246448284433)
                ·
                  refine ⟨2715395243515684836213325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620526991354246448284433 2715395243515684836213325)
                  ·
                    refine ⟨1018273216318381813579997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2715395243515684836213325 1018273216318381813579997)
                    ·
                      refine ⟨381852456119393180092499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1018273216318381813579997 381852456119393180092499)
                      ·
                        rfl

theorem cell23_743655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_743655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743655 prefixEnd_743655 := by exact prefixLift 743655
  have htrace : WordTrace (prefixWord ++ tailWord_743655) baseStart_743655 baseEnd_743655 := by
    simpa [prefixWord, tailWord_743655, baseEnd_743655] using wordTrace_append hprefix tailTrace_743655
  have hstable : (prefixWord ++ tailWord_743655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743655).length < 2 ^ (prefixWord ++ tailWord_743655).sum := by decide
  have hdescent : baseEnd_743655 < baseStart_743655 := by decide
  rcases family_descends (prefixWord ++ tailWord_743655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743691 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 6]
def baseStart_743691 : Nat := 118140960795 + 743691 * 2 ^ 59
def prefixEnd_743691 : Nat := 4983230072969 + 3 ^ 40 * 743691 * 2
def baseEnd_743691 : Nat := 381870941422955039242333

theorem tailTrace_743691 : CollatzResearch.WordTrace tailWord_743691 prefixEnd_743691 381870941422955039242333 := by
  unfold tailWord_743691
  simp only [CollatzResearch.WordTrace]
  refine ⟨27124639148741994155942927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18083092765827996103961951 27124639148741994155942927)
  ·
    refine ⟨40686958723112991233914391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27124639148741994155942927 40686958723112991233914391)
    ·
      refine ⟨61030438084669486850871587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40686958723112991233914391 61030438084669486850871587)
      ·
        refine ⟨91545657127004230276307381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61030438084669486850871587 91545657127004230276307381)
        ·
          refine ⟨8582405355656646588403817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91545657127004230276307381 8582405355656646588403817)
          ·
            refine ⟨6436804016742484941302863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8582405355656646588403817 6436804016742484941302863)
            ·
              refine ⟨9655206025113727411954295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6436804016742484941302863 9655206025113727411954295)
              ·
                refine ⟨14482809037670591117931443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9655206025113727411954295 14482809037670591117931443)
                ·
                  refine ⟨21724213556505886676897165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14482809037670591117931443 21724213556505886676897165)
                  ·
                    refine ⟨8146580083689707503836437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21724213556505886676897165 8146580083689707503836437)
                    ·
                      refine ⟨381870941422955039242333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8146580083689707503836437 381870941422955039242333)
                      ·
                        rfl

theorem cell23_743691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_743691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743691 prefixEnd_743691 := by exact prefixLift 743691
  have htrace : WordTrace (prefixWord ++ tailWord_743691) baseStart_743691 baseEnd_743691 := by
    simpa [prefixWord, tailWord_743691, baseEnd_743691] using wordTrace_append hprefix tailTrace_743691
  have hstable : (prefixWord ++ tailWord_743691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743691).length < 2 ^ (prefixWord ++ tailWord_743691).sum := by decide
  have hdescent : baseEnd_743691 < baseStart_743691 := by decide
  rcases family_descends (prefixWord ++ tailWord_743691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743762 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_743762 : Nat := 118140960795 + 743762 * 2 ^ 59
def prefixEnd_743762 : Nat := 4983230072969 + 3 ^ 40 * 743762 * 2
def baseEnd_743762 : Nat := 381907398549424261454507

theorem tailTrace_743762 : CollatzResearch.WordTrace tailWord_743762 prefixEnd_743762 381907398549424261454507 := by
  unfold tailWord_743762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6781807182871193320444385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18084819154323182187851693 6781807182871193320444385)
  ·
    refine ⟨5086355387153394990333289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6781807182871193320444385 5086355387153394990333289)
    ·
      refine ⟨3814766540365046242749967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5086355387153394990333289 3814766540365046242749967)
      ·
        refine ⟨5722149810547569364124951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3814766540365046242749967 5722149810547569364124951)
        ·
          refine ⟨8583224715821354046187427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5722149810547569364124951 8583224715821354046187427)
          ·
            refine ⟨12874837073732031069281141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8583224715821354046187427 12874837073732031069281141)
            ·
              refine ⟨1207015975662377912745107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12874837073732031069281141 1207015975662377912745107)
              ·
                refine ⟨1810523963493566869117661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207015975662377912745107 1810523963493566869117661)
                ·
                  refine ⟨678946486310087575919123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1810523963493566869117661 678946486310087575919123)
                  ·
                    refine ⟨1018419729465131363878685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 678946486310087575919123 1018419729465131363878685)
                    ·
                      refine ⟨381907398549424261454507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1018419729465131363878685 381907398549424261454507)
                      ·
                        rfl

theorem cell23_743762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_743762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743762 prefixEnd_743762 := by exact prefixLift 743762
  have htrace : WordTrace (prefixWord ++ tailWord_743762) baseStart_743762 baseEnd_743762 := by
    simpa [prefixWord, tailWord_743762, baseEnd_743762] using wordTrace_append hprefix tailTrace_743762
  have hstable : (prefixWord ++ tailWord_743762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743762).length < 2 ^ (prefixWord ++ tailWord_743762).sum := by decide
  have hdescent : baseEnd_743762 < baseStart_743762 := by decide
  rcases family_descends (prefixWord ++ tailWord_743762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743805 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_743805 : Nat := 118140960795 + 743805 * 2 ^ 59
def prefixEnd_743805 : Nat := 4983230072969 + 3 ^ 40 * 743805 * 2
def baseEnd_743805 : Nat := 381929478217567593216809

theorem tailTrace_743805 : CollatzResearch.WordTrace tailWord_743805 prefixEnd_743805 381929478217567593216809 := by
  unfold tailWord_743805
  simp only [CollatzResearch.WordTrace]
  refine ⟨27128797070328991625592869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18085864713552661083728579 27128797070328991625592869)
  ·
    refine ⟨5086649450686685929798663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27128797070328991625592869 5086649450686685929798663)
    ·
      refine ⟨7629974176030028894697995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5086649450686685929798663 7629974176030028894697995)
      ·
        refine ⟨11444961264045043342046993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7629974176030028894697995 11444961264045043342046993)
        ·
          refine ⟨8583720948033782506535245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11444961264045043342046993 8583720948033782506535245)
          ·
            refine ⟨3218895355512668439950717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8583720948033782506535245 3218895355512668439950717)
            ·
              refine ⟨1207085758317250664981519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3218895355512668439950717 1207085758317250664981519)
              ·
                refine ⟨1810628637475875997472279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207085758317250664981519 1810628637475875997472279)
                ·
                  refine ⟨2715942956213813996208419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810628637475875997472279 2715942956213813996208419)
                  ·
                    refine ⟨4073914434320720994312629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2715942956213813996208419 4073914434320720994312629)
                    ·
                      refine ⟨381929478217567593216809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4073914434320720994312629 381929478217567593216809)
                      ·
                        rfl

theorem cell23_743805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_743805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743805 prefixEnd_743805 := by exact prefixLift 743805
  have htrace : WordTrace (prefixWord ++ tailWord_743805) baseStart_743805 baseEnd_743805 := by
    simpa [prefixWord, tailWord_743805, baseEnd_743805] using wordTrace_append hprefix tailTrace_743805
  have hstable : (prefixWord ++ tailWord_743805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743805).length < 2 ^ (prefixWord ++ tailWord_743805).sum := by decide
  have hdescent : baseEnd_743805 < baseStart_743805 := by decide
  rcases family_descends (prefixWord ++ tailWord_743805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743812 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_743812 : Nat := 118140960795 + 743812 * 2 ^ 59
def prefixEnd_743812 : Nat := 4983230072969 + 3 ^ 40 * 743812 * 2
def baseEnd_743812 : Nat := 127311024194049688609759

theorem tailTrace_743812 : CollatzResearch.WordTrace tailWord_743812 prefixEnd_743812 127311024194049688609759 := by
  unfold tailWord_743812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13564526190651815910548845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18086034920869087880731793 13564526190651815910548845)
  ·
    refine ⟨5086697321494430966455817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13564526190651815910548845 5086697321494430966455817)
    ·
      refine ⟨3815022991120823224841863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5086697321494430966455817 3815022991120823224841863)
      ·
        refine ⟨5722534486681234837262795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815022991120823224841863 5722534486681234837262795)
        ·
          refine ⟨8583801730021852255894193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5722534486681234837262795 8583801730021852255894193)
          ·
            refine ⟨6437851297516389191920645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8583801730021852255894193 6437851297516389191920645)
            ·
              refine ⟨1207097118284322973485121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6437851297516389191920645 1207097118284322973485121)
              ·
                refine ⟨905322838713242230113841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207097118284322973485121 905322838713242230113841)
                ·
                  refine ⟨678992129034931672585381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 905322838713242230113841 678992129034931672585381)
                  ·
                    refine ⟨127311024194049688609759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 678992129034931672585381 127311024194049688609759)
                    ·
                      rfl

theorem cell23_743812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_743812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743812 prefixEnd_743812 := by exact prefixLift 743812
  have htrace : WordTrace (prefixWord ++ tailWord_743812) baseStart_743812 baseEnd_743812 := by
    simpa [prefixWord, tailWord_743812, baseEnd_743812] using wordTrace_append hprefix tailTrace_743812
  have hstable : (prefixWord ++ tailWord_743812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743812).length < 2 ^ (prefixWord ++ tailWord_743812).sum := by decide
  have hdescent : baseEnd_743812 < baseStart_743812 := by decide
  rcases family_descends (prefixWord ++ tailWord_743812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743822 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_743822 : Nat := 118140960795 + 743822 * 2 ^ 59
def prefixEnd_743822 : Nat := 4983230072969 + 3 ^ 40 * 743822 * 2
def baseEnd_743822 : Nat := 381938207388694026704231

theorem tailTrace_743822 : CollatzResearch.WordTrace tailWord_743822 prefixEnd_743822 381938207388694026704231 := by
  unfold tailWord_743822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391177138908425441120215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18086278074178269019307813 3391177138908425441120215)
  ·
    refine ⟨5086765708362638161680323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3391177138908425441120215 5086765708362638161680323)
    ·
      refine ⟨7630148562543957242520485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5086765708362638161680323 7630148562543957242520485)
      ·
        refine ⟨1430652855476991982972591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7630148562543957242520485 1430652855476991982972591)
        ·
          refine ⟨2145979283215487974458887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430652855476991982972591 2145979283215487974458887)
          ·
            refine ⟨3218968924823231961688331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145979283215487974458887 3218968924823231961688331)
            ·
              refine ⟨4828453387234847942532497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218968924823231961688331 4828453387234847942532497)
              ·
                refine ⟨3621340040426135956899373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4828453387234847942532497 3621340040426135956899373)
                ·
                  refine ⟨1358002515159800983837265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3621340040426135956899373 1358002515159800983837265)
                  ·
                    refine ⟨1018501886369850737877949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1358002515159800983837265 1018501886369850737877949)
                    ·
                      refine ⟨381938207388694026704231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1018501886369850737877949 381938207388694026704231)
                      ·
                        rfl

theorem cell23_743822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_743822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743822 prefixEnd_743822 := by exact prefixLift 743822
  have htrace : WordTrace (prefixWord ++ tailWord_743822) baseStart_743822 baseEnd_743822 := by
    simpa [prefixWord, tailWord_743822, baseEnd_743822] using wordTrace_append hprefix tailTrace_743822
  have hstable : (prefixWord ++ tailWord_743822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743822).length < 2 ^ (prefixWord ++ tailWord_743822).sum := by decide
  have hdescent : baseEnd_743822 < baseStart_743822 := by decide
  rcases family_descends (prefixWord ++ tailWord_743822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743832 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_743832 : Nat := 118140960795 + 743832 * 2 ^ 59
def prefixEnd_743832 : Nat := 4983230072969 + 3 ^ 40 * 743832 * 2
def baseEnd_743832 : Nat := 381943342195238987579185

theorem tailTrace_743832 : CollatzResearch.WordTrace tailWord_743832 prefixEnd_743832 381943342195238987579185 := by
  unfold tailWord_743832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13564890920615587618412875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18086521227487450157883833 13564890920615587618412875)
  ·
    refine ⟨20347336380923381427619313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13564890920615587618412875 20347336380923381427619313)
    ·
      refine ⟨15260502285692536070714485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20347336380923381427619313 15260502285692536070714485)
      ·
        refine ⟨1430672089283675256629483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15260502285692536070714485 1430672089283675256629483)
        ·
          refine ⟨2146008133925512884944225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430672089283675256629483 2146008133925512884944225)
          ·
            refine ⟨1609506100444134663708169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2146008133925512884944225 1609506100444134663708169)
            ·
              refine ⟨1207129575333100997781127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609506100444134663708169 1207129575333100997781127)
              ·
                refine ⟨1810694362999651496671691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207129575333100997781127 1810694362999651496671691)
                ·
                  refine ⟨2716041544499477245007537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810694362999651496671691 2716041544499477245007537)
                  ·
                    refine ⟨2037031158374607933755653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2716041544499477245007537 2037031158374607933755653)
                    ·
                      refine ⟨381943342195238987579185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2037031158374607933755653 381943342195238987579185)
                      ·
                        rfl

theorem cell23_743832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_743832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743832 prefixEnd_743832 := by exact prefixLift 743832
  have htrace : WordTrace (prefixWord ++ tailWord_743832) baseStart_743832 baseEnd_743832 := by
    simpa [prefixWord, tailWord_743832, baseEnd_743832] using wordTrace_append hprefix tailTrace_743832
  have hstable : (prefixWord ++ tailWord_743832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743832).length < 2 ^ (prefixWord ++ tailWord_743832).sum := by decide
  have hdescent : baseEnd_743832 < baseStart_743832 := by decide
  rcases family_descends (prefixWord ++ tailWord_743832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743850 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_743850 : Nat := 118140960795 + 743850 * 2 ^ 59
def prefixEnd_743850 : Nat := 4983230072969 + 3 ^ 40 * 743850 * 2
def baseEnd_743850 : Nat := 127317528282339972384701

theorem tailTrace_743850 : CollatzResearch.WordTrace tailWord_743850 prefixEnd_743850 127317528282339972384701 := by
  unfold tailWord_743850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6782609588791491077745251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18086958903443976207320669 6782609588791491077745251)
  ·
    refine ⟨10173914383187236616617877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6782609588791491077745251 10173914383187236616617877)
    ·
      refine ⟨476902236711901716403963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10173914383187236616617877 476902236711901716403963)
      ·
        refine ⟨715353355067852574605945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476902236711901716403963 715353355067852574605945)
        ·
          refine ⟨536515016300889430954459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715353355067852574605945 536515016300889430954459)
          ·
            refine ⟨804772524451334146431689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536515016300889430954459 804772524451334146431689)
            ·
              refine ⟨603579393338500609823767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804772524451334146431689 603579393338500609823767)
              ·
                refine ⟨905369090007750914735651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603579393338500609823767 905369090007750914735651)
                ·
                  refine ⟨1358053635011626372103477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905369090007750914735651 1358053635011626372103477)
                  ·
                    refine ⟨127317528282339972384701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1358053635011626372103477 127317528282339972384701)
                    ·
                      rfl

theorem cell23_743850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_743850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743850 prefixEnd_743850 := by exact prefixLift 743850
  have htrace : WordTrace (prefixWord ++ tailWord_743850) baseStart_743850 baseEnd_743850 := by
    simpa [prefixWord, tailWord_743850, baseEnd_743850] using wordTrace_append hprefix tailTrace_743850
  have hstable : (prefixWord ++ tailWord_743850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743850).length < 2 ^ (prefixWord ++ tailWord_743850).sum := by decide
  have hdescent : baseEnd_743850 < baseStart_743850 := by decide
  rcases family_descends (prefixWord ++ tailWord_743850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743853 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_743853 : Nat := 118140960795 + 743853 * 2 ^ 59
def prefixEnd_743853 : Nat := 4983230072969 + 3 ^ 40 * 743853 * 2
def baseEnd_743853 : Nat := 381954125288983405416589

theorem tailTrace_743853 : CollatzResearch.WordTrace tailWord_743853 prefixEnd_743853 381954125288983405416589 := by
  unfold tailWord_743853
  simp only [CollatzResearch.WordTrace]
  refine ⟨27130547774155095823340213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18087031849436730548893475 27130547774155095823340213)
  ·
    refine ⟨2543488853827040233438145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27130547774155095823340213 2543488853827040233438145)
    ·
      refine ⟨1907616640370280175078609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2543488853827040233438145 1907616640370280175078609)
      ·
        refine ⟨1430712480277710131308957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1907616640370280175078609 1430712480277710131308957)
        ·
          refine ⟨536517180104141299240859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1430712480277710131308957 536517180104141299240859)
          ·
            refine ⟨804775770156211948861289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536517180104141299240859 804775770156211948861289)
            ·
              refine ⟨603581827617158961645967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804775770156211948861289 603581827617158961645967)
              ·
                refine ⟨905372741425738442468951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603581827617158961645967 905372741425738442468951)
                ·
                  refine ⟨1358059112138607663703427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905372741425738442468951 1358059112138607663703427)
                  ·
                    refine ⟨2037088668207911495555141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1358059112138607663703427 2037088668207911495555141)
                    ·
                      refine ⟨381954125288983405416589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2037088668207911495555141 381954125288983405416589)
                      ·
                        rfl

theorem cell23_743853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_743853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743853 prefixEnd_743853 := by exact prefixLift 743853
  have htrace : WordTrace (prefixWord ++ tailWord_743853) baseStart_743853 baseEnd_743853 := by
    simpa [prefixWord, tailWord_743853, baseEnd_743853] using wordTrace_append hprefix tailTrace_743853
  have hstable : (prefixWord ++ tailWord_743853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743853).length < 2 ^ (prefixWord ++ tailWord_743853).sum := by decide
  have hdescent : baseEnd_743853 < baseStart_743853 := by decide
  rcases family_descends (prefixWord ++ tailWord_743853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743869 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_743869 : Nat := 118140960795 + 743869 * 2 ^ 59
def prefixEnd_743869 : Nat := 4983230072969 + 3 ^ 40 * 743869 * 2
def baseEnd_743869 : Nat := 381962340979455342816515

theorem tailTrace_743869 : CollatzResearch.WordTrace tailWord_743869 prefixEnd_743869 381962340979455342816515 := by
  unfold tailWord_743869
  simp only [CollatzResearch.WordTrace]
  refine ⟨27131131342097130555922661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18087420894731420370615107 27131131342097130555922661)
  ·
    refine ⟨5087087126643211979235499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27131131342097130555922661 5087087126643211979235499)
    ·
      refine ⟨7630630689964817968853249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5087087126643211979235499 7630630689964817968853249)
      ·
        refine ⟨5722973017473613476639937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7630630689964817968853249 5722973017473613476639937)
        ·
          refine ⟨4292229763105210107479953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5722973017473613476639937 4292229763105210107479953)
          ·
            refine ⟨3219172322328907580609965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4292229763105210107479953 3219172322328907580609965)
            ·
              refine ⟨1207189620873340342728737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3219172322328907580609965 1207189620873340342728737)
              ·
                refine ⟨905392215655005257046553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207189620873340342728737 905392215655005257046553)
                ·
                  refine ⟨679044161741253942784915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 905392215655005257046553 679044161741253942784915)
                  ·
                    refine ⟨1018566242611880914177373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679044161741253942784915 1018566242611880914177373)
                    ·
                      refine ⟨381962340979455342816515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1018566242611880914177373 381962340979455342816515)
                      ·
                        rfl

theorem cell23_743869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_743869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743869 prefixEnd_743869 := by exact prefixLift 743869
  have htrace : WordTrace (prefixWord ++ tailWord_743869) baseStart_743869 baseEnd_743869 := by
    simpa [prefixWord, tailWord_743869, baseEnd_743869] using wordTrace_append hprefix tailTrace_743869
  have hstable : (prefixWord ++ tailWord_743869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743869).length < 2 ^ (prefixWord ++ tailWord_743869).sum := by decide
  have hdescent : baseEnd_743869 < baseStart_743869 := by decide
  rcases family_descends (prefixWord ++ tailWord_743869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743926 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_743926 : Nat := 118140960795 + 743926 * 2 ^ 59
def prefixEnd_743926 : Nat := 4983230072969 + 3 ^ 40 * 743926 * 2
def baseEnd_743926 : Nat := 381991609376761619803753

theorem tailTrace_743926 : CollatzResearch.WordTrace tailWord_743926 prefixEnd_743926 381991609376761619803753 := by
  unfold tailWord_743926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695825643930664330671727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18088806868593752860498421 1695825643930664330671727)
  ·
    refine ⟨2543738465895996496007591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695825643930664330671727 2543738465895996496007591)
    ·
      refine ⟨3815607698843994744011387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2543738465895996496007591 3815607698843994744011387)
      ·
        refine ⟨5723411548265992116017081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815607698843994744011387 5723411548265992116017081)
        ·
          refine ⟨4292558661199494087012811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5723411548265992116017081 4292558661199494087012811)
          ·
            refine ⟨6438837991799241130519217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292558661199494087012811 6438837991799241130519217)
            ·
              refine ⟨4829128493849430847889413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6438837991799241130519217 4829128493849430847889413)
              ·
                refine ⟨905461592596768283979265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4829128493849430847889413 905461592596768283979265)
                ·
                  refine ⟨679096194447576212984449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 905461592596768283979265 679096194447576212984449)
                  ·
                    refine ⟨509322145835682159738337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 679096194447576212984449 509322145835682159738337)
                    ·
                      refine ⟨381991609376761619803753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509322145835682159738337 381991609376761619803753)
                      ·
                        rfl

theorem cell23_743926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_743926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743926 prefixEnd_743926 := by exact prefixLift 743926
  have htrace : WordTrace (prefixWord ++ tailWord_743926) baseStart_743926 baseEnd_743926 := by
    simpa [prefixWord, tailWord_743926, baseEnd_743926] using wordTrace_append hprefix tailTrace_743926
  have hstable : (prefixWord ++ tailWord_743926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743926).length < 2 ^ (prefixWord ++ tailWord_743926).sum := by decide
  have hdescent : baseEnd_743926 < baseStart_743926 := by decide
  rcases family_descends (prefixWord ++ tailWord_743926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743992 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 3, 4]
def baseStart_743992 : Nat := 118140960795 + 743992 * 2 ^ 59
def prefixEnd_743992 : Nat := 4983230072969 + 3 ^ 40 * 743992 * 2
def baseEnd_743992 : Nat := 127341833033319453859483

theorem tailTrace_743992 : CollatzResearch.WordTrace tailWord_743992 prefixEnd_743992 127341833033319453859483 := by
  unfold tailWord_743992
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567808760325761281325115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18090411680434348375100153 13567808760325761281325115)
  ·
    refine ⟨20351713140488641921987673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13567808760325761281325115 20351713140488641921987673)
    ·
      refine ⟨15263784855366481441490755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20351713140488641921987673 15263784855366481441490755)
      ·
        refine ⟨22895677283049722162236133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15263784855366481441490755 22895677283049722162236133)
        ·
          refine ⟨4292939490571822905419275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22895677283049722162236133 4292939490571822905419275)
          ·
            refine ⟨6439409235857734358128913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292939490571822905419275 6439409235857734358128913)
            ·
              refine ⟨4829556926893300768596685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6439409235857734358128913 4829556926893300768596685)
              ·
                refine ⟨1811083847584987788223757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4829556926893300768596685 1811083847584987788223757)
                ·
                  refine ⟨679156442844370420583909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1811083847584987788223757 679156442844370420583909)
                  ·
                    refine ⟨127341833033319453859483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 679156442844370420583909 127341833033319453859483)
                    ·
                      rfl

theorem cell23_743992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_743992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_743992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_743992 prefixEnd_743992 := by exact prefixLift 743992
  have htrace : WordTrace (prefixWord ++ tailWord_743992) baseStart_743992 baseEnd_743992 := by
    simpa [prefixWord, tailWord_743992, baseEnd_743992] using wordTrace_append hprefix tailTrace_743992
  have hstable : (prefixWord ++ tailWord_743992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743992).length < 2 ^ (prefixWord ++ tailWord_743992).sum := by decide
  have hdescent : baseEnd_743992 < baseStart_743992 := by decide
  rcases family_descends (prefixWord ++ tailWord_743992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744069 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_744069 : Nat := 118140960795 + 744069 * 2 ^ 59
def prefixEnd_744069 : Nat := 4983230072969 + 3 ^ 40 * 744069 * 2
def baseEnd_744069 : Nat := 127355012370118186771865

theorem tailTrace_744069 : CollatzResearch.WordTrace tailWord_744069 prefixEnd_744069 127355012370118186771865 := by
  unfold tailWord_744069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27138425941372564713203261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18092283960915043142135507 27138425941372564713203261)
  ·
    refine ⟨10176909728014711767451223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27138425941372564713203261 10176909728014711767451223)
    ·
      refine ⟨15265364592022067651176835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10176909728014711767451223 15265364592022067651176835)
      ·
        refine ⟨22898046888033101476765253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15265364592022067651176835 22898046888033101476765253)
        ·
          refine ⟨4293383791506206526893485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22898046888033101476765253 4293383791506206526893485)
          ·
            refine ⟨1610018921814827447585057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4293383791506206526893485 1610018921814827447585057)
            ·
              refine ⟨1207514191361120585688793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1610018921814827447585057 1207514191361120585688793)
              ·
                refine ⟨905635643520840439266595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207514191361120585688793 905635643520840439266595)
                ·
                  refine ⟨1358453465281260658899893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905635643520840439266595 1358453465281260658899893)
                  ·
                    refine ⟨127355012370118186771865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1358453465281260658899893 127355012370118186771865)
                    ·
                      rfl

theorem cell23_744069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_744069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744069 prefixEnd_744069 := by exact prefixLift 744069
  have htrace : WordTrace (prefixWord ++ tailWord_744069) baseStart_744069 baseEnd_744069 := by
    simpa [prefixWord, tailWord_744069, baseEnd_744069] using wordTrace_append hprefix tailTrace_744069
  have hstable : (prefixWord ++ tailWord_744069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744069).length < 2 ^ (prefixWord ++ tailWord_744069).sum := by decide
  have hdescent : baseEnd_744069 < baseStart_744069 := by decide
  rcases family_descends (prefixWord ++ tailWord_744069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744105 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_744105 : Nat := 118140960795 + 744105 * 2 ^ 59
def prefixEnd_744105 : Nat := 4983230072969 + 3 ^ 40 * 744105 * 2
def baseEnd_744105 : Nat := 382083522413916419465429

theorem tailTrace_744105 : CollatzResearch.WordTrace tailWord_744105 prefixEnd_744105 382083522413916419465429 := by
  unfold tailWord_744105
  simp only [CollatzResearch.WordTrace]
  refine ⟨27139738969242142861513769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18093159312828095241009179 27139738969242142861513769)
  ·
    refine ⟨20354804226931607146135327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27139738969242142861513769 20354804226931607146135327)
    ·
      refine ⟨30532206340397410719202991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20354804226931607146135327 30532206340397410719202991)
      ·
        refine ⟨45798309510596116078804487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30532206340397410719202991 45798309510596116078804487)
        ·
          refine ⟨68697464265894174118206731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45798309510596116078804487 68697464265894174118206731)
          ·
            refine ⟨103046196398841261177310097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68697464265894174118206731 103046196398841261177310097)
            ·
              refine ⟨77284647299130945882982573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103046196398841261177310097 77284647299130945882982573)
              ·
                refine ⟨28981742737174104706118465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77284647299130945882982573 28981742737174104706118465)
                ·
                  refine ⟨21736307052880578529588849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28981742737174104706118465 21736307052880578529588849)
                  ·
                    refine ⟨16302230289660433897191637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21736307052880578529588849 16302230289660433897191637)
                    ·
                      refine ⟨382083522413916419465429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16302230289660433897191637 382083522413916419465429)
                      ·
                        rfl

theorem cell23_744105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_744105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744105 prefixEnd_744105 := by exact prefixLift 744105
  have htrace : WordTrace (prefixWord ++ tailWord_744105) baseStart_744105 baseEnd_744105 := by
    simpa [prefixWord, tailWord_744105, baseEnd_744105] using wordTrace_append hprefix tailTrace_744105
  have hstable : (prefixWord ++ tailWord_744105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744105).length < 2 ^ (prefixWord ++ tailWord_744105).sum := by decide
  have hdescent : baseEnd_744105 < baseStart_744105 := by decide
  rcases family_descends (prefixWord ++ tailWord_744105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744109 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_744109 : Nat := 118140960795 + 744109 * 2 ^ 59
def prefixEnd_744109 : Nat := 4983230072969 + 3 ^ 40 * 744109 * 2
def baseEnd_744109 : Nat := 382085576336534403815411

theorem tailTrace_744109 : CollatzResearch.WordTrace tailWord_744109 prefixEnd_744109 382085576336534403815411 := by
  unfold tailWord_744109
  simp only [CollatzResearch.WordTrace]
  refine ⟨27139884861227651544659381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18093256574151767696439587 27139884861227651544659381)
  ·
    refine ⟨2544364205740092332311817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27139884861227651544659381 2544364205740092332311817)
    ·
      refine ⟨1908273154305069249233863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2544364205740092332311817 1908273154305069249233863)
      ·
        refine ⟨2862409731457603873850795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908273154305069249233863 2862409731457603873850795)
        ·
          refine ⟨4293614597186405810776193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862409731457603873850795 4293614597186405810776193)
          ·
            refine ⟨3220210947889804358082145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4293614597186405810776193 3220210947889804358082145)
            ·
              refine ⟨2415158210917353268561609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3220210947889804358082145 2415158210917353268561609)
              ·
                refine ⟨1811368658188014951421207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415158210917353268561609 1811368658188014951421207)
                ·
                  refine ⟨2717052987282022427131811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811368658188014951421207 2717052987282022427131811)
                  ·
                    refine ⟨4075579480923033640697717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2717052987282022427131811 4075579480923033640697717)
                    ·
                      refine ⟨382085576336534403815411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4075579480923033640697717 382085576336534403815411)
                      ·
                        rfl

theorem cell23_744109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_744109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744109 prefixEnd_744109 := by exact prefixLift 744109
  have htrace : WordTrace (prefixWord ++ tailWord_744109) baseStart_744109 baseEnd_744109 := by
    simpa [prefixWord, tailWord_744109, baseEnd_744109] using wordTrace_append hprefix tailTrace_744109
  have hstable : (prefixWord ++ tailWord_744109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744109).length < 2 ^ (prefixWord ++ tailWord_744109).sum := by decide
  have hdescent : baseEnd_744109 < baseStart_744109 := by decide
  rcases family_descends (prefixWord ++ tailWord_744109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744192 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_744192 : Nat := 118140960795 + 744192 * 2 ^ 59
def prefixEnd_744192 : Nat := 4983230072969 + 3 ^ 40 * 744192 * 2
def baseEnd_744192 : Nat := 382128195230857579077529

theorem tailTrace_744192 : CollatzResearch.WordTrace tailWord_744192 prefixEnd_744192 382128195230857579077529 := by
  unfold tailWord_744192
  simp only [CollatzResearch.WordTrace]
  refine ⟨13571456059963478359965415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18095274746617971146620553 13571456059963478359965415)
  ·
    refine ⟨20357184089945217539948123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13571456059963478359965415 20357184089945217539948123)
    ·
      refine ⟨30535776134917826309922185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20357184089945217539948123 30535776134917826309922185)
      ·
        refine ⟨22901832101188369732441639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30535776134917826309922185 22901832101188369732441639)
        ·
          refine ⟨34352748151782554598662459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22901832101188369732441639 34352748151782554598662459)
          ·
            refine ⟨51529122227673831897993689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34352748151782554598662459 51529122227673831897993689)
            ·
              refine ⟨38646841670755373923495267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51529122227673831897993689 38646841670755373923495267)
              ·
                refine ⟨57970262506133060885242901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38646841670755373923495267 57970262506133060885242901)
                ·
                  refine ⟨2717356054974987228995761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57970262506133060885242901 2717356054974987228995761)
                  ·
                    refine ⟨2038017041231240421746821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2717356054974987228995761 2038017041231240421746821)
                    ·
                      refine ⟨382128195230857579077529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2038017041231240421746821 382128195230857579077529)
                      ·
                        rfl

theorem cell23_744192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_744192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744192 prefixEnd_744192 := by exact prefixLift 744192
  have htrace : WordTrace (prefixWord ++ tailWord_744192) baseStart_744192 baseEnd_744192 := by
    simpa [prefixWord, tailWord_744192, baseEnd_744192] using wordTrace_append hprefix tailTrace_744192
  have hstable : (prefixWord ++ tailWord_744192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744192).length < 2 ^ (prefixWord ++ tailWord_744192).sum := by decide
  have hdescent : baseEnd_744192 < baseStart_744192 := by decide
  rcases family_descends (prefixWord ++ tailWord_744192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744196 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_744196 : Nat := 118140960795 + 744196 * 2 ^ 59
def prefixEnd_744196 : Nat := 4983230072969 + 3 ^ 40 * 744196 * 2
def baseEnd_744196 : Nat := 382130249153475563427511

theorem tailTrace_744196 : CollatzResearch.WordTrace tailWord_744196 prefixEnd_744196 382130249153475563427511 := by
  unfold tailWord_744196
  simp only [CollatzResearch.WordTrace]
  refine ⟨13571529005956232701538221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18095372007941643602050961 13571529005956232701538221)
  ·
    refine ⟨5089323377233587263076833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13571529005956232701538221 5089323377233587263076833)
    ·
      refine ⟨3816992532925190447307625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5089323377233587263076833 3816992532925190447307625)
      ·
        refine ⟨2862744399693892835480719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3816992532925190447307625 2862744399693892835480719)
        ·
          refine ⟨4294116599540839253221079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862744399693892835480719 4294116599540839253221079)
          ·
            refine ⟨6441174899311258879831619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294116599540839253221079 6441174899311258879831619)
            ·
              refine ⟨9661762348966888319747429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441174899311258879831619 9661762348966888319747429)
              ·
                refine ⟨1811580440431291559952643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9661762348966888319747429 1811580440431291559952643)
                ·
                  refine ⟨2717370660646937339928965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811580440431291559952643 2717370660646937339928965)
                  ·
                    refine ⟨509506998871300751236681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717370660646937339928965 509506998871300751236681)
                    ·
                      refine ⟨382130249153475563427511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509506998871300751236681 382130249153475563427511)
                      ·
                        rfl

theorem cell23_744196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_744196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744196 prefixEnd_744196 := by exact prefixLift 744196
  have htrace : WordTrace (prefixWord ++ tailWord_744196) baseStart_744196 baseEnd_744196 := by
    simpa [prefixWord, tailWord_744196, baseEnd_744196] using wordTrace_append hprefix tailTrace_744196
  have hstable : (prefixWord ++ tailWord_744196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744196).length < 2 ^ (prefixWord ++ tailWord_744196).sum := by decide
  have hdescent : baseEnd_744196 < baseStart_744196 := by decide
  rcases family_descends (prefixWord ++ tailWord_744196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744200 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_744200 : Nat := 118140960795 + 744200 * 2 ^ 59
def prefixEnd_744200 : Nat := 4983230072969 + 3 ^ 40 * 744200 * 2
def baseEnd_744200 : Nat := 382132303076093547777493

theorem tailTrace_744200 : CollatzResearch.WordTrace tailWord_744200 prefixEnd_744200 382132303076093547777493 := by
  unfold tailWord_744200
  simp only [CollatzResearch.WordTrace]
  refine ⟨13571601951948987043111027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18095469269265316057481369 13571601951948987043111027)
  ·
    refine ⟨20357402927923480564666541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13571601951948987043111027 20357402927923480564666541)
    ·
      refine ⟨7634026097971305211749953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20357402927923480564666541 7634026097971305211749953)
      ·
        refine ⟨5725519573478478908812465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7634026097971305211749953 5725519573478478908812465)
        ·
          refine ⟨4294139680108859181609349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5725519573478478908812465 4294139680108859181609349)
          ·
            refine ⟨805151190020411096551753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4294139680108859181609349 805151190020411096551753)
            ·
              refine ⟨603863392515308322413815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805151190020411096551753 603863392515308322413815)
              ·
                refine ⟨905795088772962483620723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603863392515308322413815 905795088772962483620723)
                ·
                  refine ⟨1358692633159443725431085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905795088772962483620723 1358692633159443725431085)
                  ·
                    refine ⟨509509737434791397036657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358692633159443725431085 509509737434791397036657)
                    ·
                      refine ⟨382132303076093547777493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509509737434791397036657 382132303076093547777493)
                      ·
                        rfl

theorem cell23_744200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_744200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744200 prefixEnd_744200 := by exact prefixLift 744200
  have htrace : WordTrace (prefixWord ++ tailWord_744200) baseStart_744200 baseEnd_744200 := by
    simpa [prefixWord, tailWord_744200, baseEnd_744200] using wordTrace_append hprefix tailTrace_744200
  have hstable : (prefixWord ++ tailWord_744200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744200).length < 2 ^ (prefixWord ++ tailWord_744200).sum := by decide
  have hdescent : baseEnd_744200 < baseStart_744200 := by decide
  rcases family_descends (prefixWord ++ tailWord_744200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744202 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 9]
def baseStart_744202 : Nat := 118140960795 + 744202 * 2 ^ 59
def prefixEnd_744202 : Nat := 4983230072969 + 3 ^ 40 * 744202 * 2
def baseEnd_744202 : Nat := 42459258893044726661387

theorem tailTrace_744202 : CollatzResearch.WordTrace tailWord_744202 prefixEnd_744202 42459258893044726661387 := by
  unfold tailWord_744202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6785819212472682106948715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18095517899927152285196573 6785819212472682106948715)
  ·
    refine ⟨10178728818709023160423073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6785819212472682106948715 10178728818709023160423073)
    ·
      refine ⟨7634046614031767370317305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10178728818709023160423073 7634046614031767370317305)
      ·
        refine ⟨5725534960523825527737979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7634046614031767370317305 5725534960523825527737979)
        ·
          refine ⟨8588302440785738291606969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5725534960523825527737979 8588302440785738291606969)
          ·
            refine ⟨6441226830589303718705227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8588302440785738291606969 6441226830589303718705227)
            ·
              refine ⟨9661840245883955578057841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441226830589303718705227 9661840245883955578057841)
              ·
                refine ⟨7246380184412966683543381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9661840245883955578057841 7246380184412966683543381)
                ·
                  refine ⟨42459258893044726661387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7246380184412966683543381 42459258893044726661387)
                  ·
                    rfl

theorem cell23_744202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_744202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744202 prefixEnd_744202 := by exact prefixLift 744202
  have htrace : WordTrace (prefixWord ++ tailWord_744202) baseStart_744202 baseEnd_744202 := by
    simpa [prefixWord, tailWord_744202, baseEnd_744202] using wordTrace_append hprefix tailTrace_744202
  have hstable : (prefixWord ++ tailWord_744202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744202).length < 2 ^ (prefixWord ++ tailWord_744202).sum := by decide
  have hdescent : baseEnd_744202 < baseStart_744202 := by decide
  rcases family_descends (prefixWord ++ tailWord_744202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744229 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_744229 : Nat := 118140960795 + 744229 * 2 ^ 59
def prefixEnd_744229 : Nat := 4983230072969 + 3 ^ 40 * 744229 * 2
def baseEnd_744229 : Nat := 382147194015073934314859

theorem tailTrace_744229 : CollatzResearch.WordTrace tailWord_744229 prefixEnd_744229 382147194015073934314859 := by
  unfold tailWord_744229
  simp only [CollatzResearch.WordTrace]
  refine ⟨27144261620792912039027741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18096174413861941359351827 27144261620792912039027741)
  ·
    refine ⟨10179098107797342014635403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27144261620792912039027741 10179098107797342014635403)
    ·
      refine ⟨15268647161696013021953105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10179098107797342014635403 15268647161696013021953105)
      ·
        refine ⟨11451485371272009766464829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15268647161696013021953105 11451485371272009766464829)
        ·
          refine ⟨4294307014227003662424311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11451485371272009766464829 4294307014227003662424311)
          ·
            refine ⟨6441460521340505493636467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294307014227003662424311 6441460521340505493636467)
            ·
              refine ⟨9662190782010758240454701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441460521340505493636467 9662190782010758240454701)
              ·
                refine ⟨3623321543254034340170513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9662190782010758240454701 3623321543254034340170513)
                ·
                  refine ⟨2717491157440525755127885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3623321543254034340170513 2717491157440525755127885)
                  ·
                    refine ⟨1019059184040197158172957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2717491157440525755127885 1019059184040197158172957)
                    ·
                      refine ⟨382147194015073934314859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1019059184040197158172957 382147194015073934314859)
                      ·
                        rfl

theorem cell23_744229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_744229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744229 prefixEnd_744229 := by exact prefixLift 744229
  have htrace : WordTrace (prefixWord ++ tailWord_744229) baseStart_744229 baseEnd_744229 := by
    simpa [prefixWord, tailWord_744229, baseEnd_744229] using wordTrace_append hprefix tailTrace_744229
  have hstable : (prefixWord ++ tailWord_744229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744229).length < 2 ^ (prefixWord ++ tailWord_744229).sum := by decide
  have hdescent : baseEnd_744229 < baseStart_744229 := by decide
  rcases family_descends (prefixWord ++ tailWord_744229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744276 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_744276 : Nat := 118140960795 + 744276 * 2 ^ 59
def prefixEnd_744276 : Nat := 4983230072969 + 3 ^ 40 * 744276 * 2
def baseEnd_744276 : Nat := 382171327605835250427143

theorem tailTrace_744276 : CollatzResearch.WordTrace tailWord_744276 prefixEnd_744276 382171327605835250427143 := by
  unfold tailWord_744276
  simp only [CollatzResearch.WordTrace]
  refine ⟨13572987925811319532994341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18097317234415092710659121 13572987925811319532994341)
  ·
    refine ⟨2544935236089622412436439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13572987925811319532994341 2544935236089622412436439)
    ·
      refine ⟨3817402854134433618654659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2544935236089622412436439 3817402854134433618654659)
      ·
        refine ⟨5726104281201650427981989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817402854134433618654659 5726104281201650427981989)
        ·
          refine ⟨1073644552725309455246623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5726104281201650427981989 1073644552725309455246623)
          ·
            refine ⟨1610466829087964182869935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073644552725309455246623 1610466829087964182869935)
            ·
              refine ⟨2415700243631946274304903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610466829087964182869935 2415700243631946274304903)
              ·
                refine ⟨3623550365447919411457355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2415700243631946274304903 3623550365447919411457355)
                ·
                  refine ⟨5435325548171879117186033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623550365447919411457355 5435325548171879117186033)
                  ·
                    refine ⟨4076494161128909337889525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5435325548171879117186033 4076494161128909337889525)
                    ·
                      refine ⟨382171327605835250427143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4076494161128909337889525 382171327605835250427143)
                      ·
                        rfl

theorem cell23_744276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_744276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744276 prefixEnd_744276 := by exact prefixLift 744276
  have htrace : WordTrace (prefixWord ++ tailWord_744276) baseStart_744276 baseEnd_744276 := by
    simpa [prefixWord, tailWord_744276, baseEnd_744276] using wordTrace_append hprefix tailTrace_744276
  have hstable : (prefixWord ++ tailWord_744276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744276).length < 2 ^ (prefixWord ++ tailWord_744276).sum := by decide
  have hdescent : baseEnd_744276 < baseStart_744276 := by decide
  rcases family_descends (prefixWord ++ tailWord_744276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744289 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_744289 : Nat := 118140960795 + 744289 * 2 ^ 59
def prefixEnd_744289 : Nat := 4983230072969 + 3 ^ 40 * 744289 * 2
def baseEnd_744289 : Nat := 382178002854343699564583

theorem tailTrace_744289 : CollatzResearch.WordTrace tailWord_744289 prefixEnd_744289 382178002854343699564583 := by
  unfold tailWord_744289
  simp only [CollatzResearch.WordTrace]
  refine ⟨27146450000575542286211921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18097633333717028190807947 27146450000575542286211921)
  ·
    refine ⟨20359837500431656714658941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27146450000575542286211921 20359837500431656714658941)
    ·
      refine ⟨7634939062661871267997103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20359837500431656714658941 7634939062661871267997103)
      ·
        refine ⟨11452408593992806901995655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7634939062661871267997103 11452408593992806901995655)
        ·
          refine ⟨17178612890989210352993483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11452408593992806901995655 17178612890989210352993483)
          ·
            refine ⟨25767919336483815529490225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17178612890989210352993483 25767919336483815529490225)
            ·
              refine ⟨19325939502362861647117669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25767919336483815529490225 19325939502362861647117669)
              ·
                refine ⟨3623613656693036558834563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19325939502362861647117669 3623613656693036558834563)
                ·
                  refine ⟨5435420485039554838251845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623613656693036558834563 5435420485039554838251845)
                  ·
                    refine ⟨1019141340944916532172221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5435420485039554838251845 1019141340944916532172221)
                    ·
                      refine ⟨382178002854343699564583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1019141340944916532172221 382178002854343699564583)
                      ·
                        rfl

theorem cell23_744289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_744289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744289 prefixEnd_744289 := by exact prefixLift 744289
  have htrace : WordTrace (prefixWord ++ tailWord_744289) baseStart_744289 baseEnd_744289 := by
    simpa [prefixWord, tailWord_744289, baseEnd_744289] using wordTrace_append hprefix tailTrace_744289
  have hstable : (prefixWord ++ tailWord_744289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744289).length < 2 ^ (prefixWord ++ tailWord_744289).sum := by decide
  have hdescent : baseEnd_744289 < baseStart_744289 := by decide
  rcases family_descends (prefixWord ++ tailWord_744289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744306 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_744306 : Nat := 118140960795 + 744306 * 2 ^ 59
def prefixEnd_744306 : Nat := 4983230072969 + 3 ^ 40 * 744306 * 2
def baseEnd_744306 : Nat := 382186732025470133052005

theorem tailTrace_744306 : CollatzResearch.WordTrace tailWord_744306 prefixEnd_744306 382186732025470133052005 := by
  unfold tailWord_744306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786767510378488547395193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18098046694342636126387181 6786767510378488547395193)
  ·
    refine ⟨5090075632783866410546395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6786767510378488547395193 5090075632783866410546395)
    ·
      refine ⟨7635113449175799615819593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5090075632783866410546395 7635113449175799615819593)
      ·
        refine ⟨5726335086881849711864695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7635113449175799615819593 5726335086881849711864695)
        ·
          refine ⟨8589502630322774567797043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726335086881849711864695 8589502630322774567797043)
          ·
            refine ⟨12884253945484161851695565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8589502630322774567797043 12884253945484161851695565)
            ·
              refine ⟨4831595229556560694385837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12884253945484161851695565 4831595229556560694385837)
              ·
                refine ⟨1811848211083710260394689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4831595229556560694385837 1811848211083710260394689)
                ·
                  refine ⟨1358886158312782695296017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1811848211083710260394689 1358886158312782695296017)
                  ·
                    refine ⟨1019164618734587021472013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1358886158312782695296017 1019164618734587021472013)
                    ·
                      refine ⟨382186732025470133052005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1019164618734587021472013 382186732025470133052005)
                      ·
                        rfl

theorem cell23_744306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_744306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744306 prefixEnd_744306 := by exact prefixLift 744306
  have htrace : WordTrace (prefixWord ++ tailWord_744306) baseStart_744306 baseEnd_744306 := by
    simpa [prefixWord, tailWord_744306, baseEnd_744306] using wordTrace_append hprefix tailTrace_744306
  have hstable : (prefixWord ++ tailWord_744306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744306).length < 2 ^ (prefixWord ++ tailWord_744306).sum := by decide
  have hdescent : baseEnd_744306 < baseStart_744306 := by decide
  rcases family_descends (prefixWord ++ tailWord_744306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744330 : List Nat := [3, 1, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_744330 : Nat := 118140960795 + 744330 * 2 ^ 59
def prefixEnd_744330 : Nat := 4983230072969 + 3 ^ 40 * 744330 * 2
def baseEnd_744330 : Nat := 127399685187059346383965

theorem tailTrace_744330 : CollatzResearch.WordTrace tailWord_744330 prefixEnd_744330 127399685187059346383965 := by
  unfold tailWord_744330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786986348356751572113611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18098630262284670858969629 6786986348356751572113611)
  ·
    refine ⟨10180479522535127358170417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6786986348356751572113611 10180479522535127358170417)
    ·
      refine ⟨7635359641901345518627813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10180479522535127358170417 7635359641901345518627813)
      ·
        refine ⟨1431629932856502284742715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7635359641901345518627813 1431629932856502284742715)
        ·
          refine ⟨2147444899284753427114073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431629932856502284742715 2147444899284753427114073)
          ·
            refine ⟨1610583674463565070335555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2147444899284753427114073 1610583674463565070335555)
            ·
              refine ⟨2415875511695347605503333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610583674463565070335555 2415875511695347605503333)
              ·
                refine ⟨452976658442877676031875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2415875511695347605503333 452976658442877676031875)
                ·
                  refine ⟨679464987664316514047813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452976658442877676031875 679464987664316514047813)
                  ·
                    refine ⟨127399685187059346383965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 679464987664316514047813 127399685187059346383965)
                    ·
                      rfl

theorem cell23_744330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_744330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744330 prefixEnd_744330 := by exact prefixLift 744330
  have htrace : WordTrace (prefixWord ++ tailWord_744330) baseStart_744330 baseEnd_744330 := by
    simpa [prefixWord, tailWord_744330, baseEnd_744330] using wordTrace_append hprefix tailTrace_744330
  have hstable : (prefixWord ++ tailWord_744330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744330).length < 2 ^ (prefixWord ++ tailWord_744330).sum := by decide
  have hdescent : baseEnd_744330 < baseStart_744330 := by decide
  rcases family_descends (prefixWord ++ tailWord_744330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744349 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_744349 : Nat := 118140960795 + 744349 * 2 ^ 59
def prefixEnd_744349 : Nat := 4983230072969 + 3 ^ 40 * 744349 * 2
def baseEnd_744349 : Nat := 382208811693613464814307

theorem tailTrace_744349 : CollatzResearch.WordTrace tailWord_744349 prefixEnd_744349 382208811693613464814307 := by
  unfold tailWord_744349
  simp only [CollatzResearch.WordTrace]
  refine ⟨27148638380358172533396101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18099092253572115022264067 27148638380358172533396101)
  ·
    refine ⟨5090369696317157350011769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27148638380358172533396101 5090369696317157350011769)
    ·
      refine ⟨3817777272237868012508827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5090369696317157350011769 3817777272237868012508827)
      ·
        refine ⟨5726665908356802018763241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817777272237868012508827 5726665908356802018763241)
        ·
          refine ⟨4294999431267601514072431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5726665908356802018763241 4294999431267601514072431)
          ·
            refine ⟨6442499146901402271108647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294999431267601514072431 6442499146901402271108647)
            ·
              refine ⟨9663748720352103406662971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442499146901402271108647 9663748720352103406662971)
              ·
                refine ⟨14495623080528155109994457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9663748720352103406662971 14495623080528155109994457)
                ·
                  refine ⟨10871717310396116332495843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14495623080528155109994457 10871717310396116332495843)
                  ·
                    refine ⟨16307575965594174498743765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10871717310396116332495843 16307575965594174498743765)
                    ·
                      refine ⟨382208811693613464814307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16307575965594174498743765 382208811693613464814307)
                      ·
                        rfl

theorem cell23_744349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_744349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744349 prefixEnd_744349 := by exact prefixLift 744349
  have htrace : WordTrace (prefixWord ++ tailWord_744349) baseStart_744349 baseEnd_744349 := by
    simpa [prefixWord, tailWord_744349, baseEnd_744349] using wordTrace_append hprefix tailTrace_744349
  have hstable : (prefixWord ++ tailWord_744349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744349).length < 2 ^ (prefixWord ++ tailWord_744349).sum := by decide
  have hdescent : baseEnd_744349 < baseStart_744349 := by decide
  rcases family_descends (prefixWord ++ tailWord_744349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744353 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_744353 : Nat := 118140960795 + 744353 * 2 ^ 59
def prefixEnd_744353 : Nat := 4983230072969 + 3 ^ 40 * 744353 * 2
def baseEnd_744353 : Nat := 382210865616231449164289

theorem tailTrace_744353 : CollatzResearch.WordTrace tailWord_744353 prefixEnd_744353 382210865616231449164289 := by
  unfold tailWord_744353
  simp only [CollatzResearch.WordTrace]
  refine ⟨27148784272343681216541713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18099189514895787477694475 27148784272343681216541713)
  ·
    refine ⟨20361588204257760912406285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27148784272343681216541713 20361588204257760912406285)
    ·
      refine ⟨7635595576596660342152357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20361588204257760912406285 7635595576596660342152357)
      ·
        refine ⟨1431674170611873814153567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7635595576596660342152357 1431674170611873814153567)
        ·
          refine ⟨2147511255917810721230351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431674170611873814153567 2147511255917810721230351)
          ·
            refine ⟨3221266883876716081845527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147511255917810721230351 3221266883876716081845527)
            ·
              refine ⟨4831900325815074122768291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221266883876716081845527 4831900325815074122768291)
              ·
                refine ⟨7247850488722611184152437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831900325815074122768291 7247850488722611184152437)
                ·
                  refine ⟨679485983317744798514291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7247850488722611184152437 679485983317744798514291)
                  ·
                    refine ⟨1019228974976617197771437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679485983317744798514291 1019228974976617197771437)
                    ·
                      refine ⟨382210865616231449164289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1019228974976617197771437 382210865616231449164289)
                      ·
                        rfl

theorem cell23_744353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_744353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744353 prefixEnd_744353 := by exact prefixLift 744353
  have htrace : WordTrace (prefixWord ++ tailWord_744353) baseStart_744353 baseEnd_744353 := by
    simpa [prefixWord, tailWord_744353, baseEnd_744353] using wordTrace_append hprefix tailTrace_744353
  have hstable : (prefixWord ++ tailWord_744353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744353).length < 2 ^ (prefixWord ++ tailWord_744353).sum := by decide
  have hdescent : baseEnd_744353 < baseStart_744353 := by decide
  rcases family_descends (prefixWord ++ tailWord_744353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744356 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_744356 : Nat := 118140960795 + 744356 * 2 ^ 59
def prefixEnd_744356 : Nat := 4983230072969 + 3 ^ 40 * 744356 * 2
def baseEnd_744356 : Nat := 127404135352731645808925

theorem tailTrace_744356 : CollatzResearch.WordTrace tailWord_744356 prefixEnd_744356 127404135352731645808925 := by
  unfold tailWord_744356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13574446845666406364450461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18099262460888541819267281 13574446845666406364450461)
  ·
    refine ⟨5090417567124902386668923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13574446845666406364450461 5090417567124902386668923)
    ·
      refine ⟨7635626350687353580003385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5090417567124902386668923 7635626350687353580003385)
      ·
        refine ⟨5726719763015515185002539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7635626350687353580003385 5726719763015515185002539)
        ·
          refine ⟨8590079644523272777503809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5726719763015515185002539 8590079644523272777503809)
          ·
            refine ⟨6442559733392454583127857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8590079644523272777503809 6442559733392454583127857)
            ·
              refine ⟨4831919800044340937345893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6442559733392454583127857 4831919800044340937345893)
              ·
                refine ⟨905984962508313925752355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4831919800044340937345893 905984962508313925752355)
                ·
                  refine ⟨1358977443762470888628533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905984962508313925752355 1358977443762470888628533)
                  ·
                    refine ⟨127404135352731645808925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1358977443762470888628533 127404135352731645808925)
                    ·
                      rfl

theorem cell23_744356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_744356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744356 prefixEnd_744356 := by exact prefixLift 744356
  have htrace : WordTrace (prefixWord ++ tailWord_744356) baseStart_744356 baseEnd_744356 := by
    simpa [prefixWord, tailWord_744356, baseEnd_744356] using wordTrace_append hprefix tailTrace_744356
  have hstable : (prefixWord ++ tailWord_744356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744356).length < 2 ^ (prefixWord ++ tailWord_744356).sum := by decide
  have hdescent : baseEnd_744356 < baseStart_744356 := by decide
  rcases family_descends (prefixWord ++ tailWord_744356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744379 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 3]
def baseStart_744379 : Nat := 118140960795 + 744379 * 2 ^ 59
def prefixEnd_744379 : Nat := 4983230072969 + 3 ^ 40 * 744379 * 2
def baseEnd_744379 : Nat := 382224216113248347439169

theorem tailTrace_744379 : CollatzResearch.WordTrace tailWord_744379 prefixEnd_744379 382224216113248347439169 := by
  unfold tailWord_744379
  simp only [CollatzResearch.WordTrace]
  refine ⟨27149732570249487656988191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18099821713499658437992127 27149732570249487656988191)
  ·
    refine ⟨40724598855374231485482287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27149732570249487656988191 40724598855374231485482287)
    ·
      refine ⟨61086898283061347228223431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40724598855374231485482287 61086898283061347228223431)
      ·
        refine ⟨91630347424592020842335147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61086898283061347228223431 91630347424592020842335147)
        ·
          refine ⟨137445521136888031263502721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91630347424592020842335147 137445521136888031263502721)
          ·
            refine ⟨103084140852666023447627041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137445521136888031263502721 103084140852666023447627041)
            ·
              refine ⟨77313105639499517585720281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103084140852666023447627041 77313105639499517585720281)
              ·
                refine ⟨57984829229624638189290211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77313105639499517585720281 57984829229624638189290211)
                ·
                  refine ⟨86977243844436957283935317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57984829229624638189290211 86977243844436957283935317)
                  ·
                    refine ⟨1019264576301995593171117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86977243844436957283935317 1019264576301995593171117)
                    ·
                      refine ⟨382224216113248347439169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1019264576301995593171117 382224216113248347439169)
                      ·
                        rfl

theorem cell23_744379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 3].length) (baseStart_744379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744379 prefixEnd_744379 := by exact prefixLift 744379
  have htrace : WordTrace (prefixWord ++ tailWord_744379) baseStart_744379 baseEnd_744379 := by
    simpa [prefixWord, tailWord_744379, baseEnd_744379] using wordTrace_append hprefix tailTrace_744379
  have hstable : (prefixWord ++ tailWord_744379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744379).length < 2 ^ (prefixWord ++ tailWord_744379).sum := by decide
  have hdescent : baseEnd_744379 < baseStart_744379 := by decide
  rcases family_descends (prefixWord ++ tailWord_744379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744396 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_744396 : Nat := 118140960795 + 744396 * 2 ^ 59
def prefixEnd_744396 : Nat := 4983230072969 + 3 ^ 40 * 744396 * 2
def baseEnd_744396 : Nat := 382232945284374780926591

theorem tailTrace_744396 : CollatzResearch.WordTrace tailWord_744396 prefixEnd_744396 382232945284374780926591 := by
  unfold tailWord_744396
  simp only [CollatzResearch.WordTrace]
  refine ⟨13575176305593949780178521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18100235074125266373571361 13575176305593949780178521)
  ·
    refine ⟨10181382229195462335133891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13575176305593949780178521 10181382229195462335133891)
    ·
      refine ⟨15272073343793193502700837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10181382229195462335133891 15272073343793193502700837)
      ·
        refine ⟨2863513751961223781756407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15272073343793193502700837 2863513751961223781756407)
        ·
          refine ⟨4295270627941835672634611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2863513751961223781756407 4295270627941835672634611)
          ·
            refine ⟨6442905941912753508951917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295270627941835672634611 6442905941912753508951917)
            ·
              refine ⟨2416089728217282565856969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6442905941912753508951917 2416089728217282565856969)
              ·
                refine ⟨1812067296162961924392727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2416089728217282565856969 1812067296162961924392727)
                ·
                  refine ⟨2718100944244442886589091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812067296162961924392727 2718100944244442886589091)
                  ·
                    refine ⟨4077151416366664329883637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2718100944244442886589091 4077151416366664329883637)
                    ·
                      refine ⟨382232945284374780926591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4077151416366664329883637 382232945284374780926591)
                      ·
                        rfl

theorem cell23_744396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_744396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744396 prefixEnd_744396 := by exact prefixLift 744396
  have htrace : WordTrace (prefixWord ++ tailWord_744396) baseStart_744396 baseEnd_744396 := by
    simpa [prefixWord, tailWord_744396, baseEnd_744396] using wordTrace_append hprefix tailTrace_744396
  have hstable : (prefixWord ++ tailWord_744396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744396).length < 2 ^ (prefixWord ++ tailWord_744396).sum := by decide
  have hdescent : baseEnd_744396 < baseStart_744396 := by decide
  rcases family_descends (prefixWord ++ tailWord_744396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744410 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2]
def baseStart_744410 : Nat := 118140960795 + 744410 * 2 ^ 59
def prefixEnd_744410 : Nat := 4983230072969 + 3 ^ 40 * 744410 * 2
def baseEnd_744410 : Nat := 382240134013537726151527

theorem tailTrace_744410 : CollatzResearch.WordTrace tailWord_744410 prefixEnd_744410 382240134013537726151527 := by
  unfold tailWord_744410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6787715808284294987841671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18100575488758119967577789 6787715808284294987841671)
  ·
    refine ⟨10181573712426442481762507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6787715808284294987841671 10181573712426442481762507)
    ·
      refine ⟨15272360568639663722643761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10181573712426442481762507 15272360568639663722643761)
      ·
        refine ⟨11454270426479747791982821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15272360568639663722643761 11454270426479747791982821)
        ·
          refine ⟨2147675704964952710996779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11454270426479747791982821 2147675704964952710996779)
          ·
            refine ⟨3221513557447429066495169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147675704964952710996779 3221513557447429066495169)
            ·
              refine ⟨2416135168085571799871377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3221513557447429066495169 2416135168085571799871377)
              ·
                refine ⟨1812101376064178849903533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2416135168085571799871377 1812101376064178849903533)
                ·
                  refine ⟨679538016024067068713825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1812101376064178849903533 679538016024067068713825)
                  ·
                    refine ⟨509653512018050301535369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 679538016024067068713825 509653512018050301535369)
                    ·
                      refine ⟨382240134013537726151527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509653512018050301535369 382240134013537726151527)
                      ·
                        rfl

theorem cell23_744410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_744410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744410 prefixEnd_744410 := by exact prefixLift 744410
  have htrace : WordTrace (prefixWord ++ tailWord_744410) baseStart_744410 baseEnd_744410 := by
    simpa [prefixWord, tailWord_744410, baseEnd_744410] using wordTrace_append hprefix tailTrace_744410
  have hstable : (prefixWord ++ tailWord_744410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744410).length < 2 ^ (prefixWord ++ tailWord_744410).sum := by decide
  have hdescent : baseEnd_744410 < baseStart_744410 := by decide
  rcases family_descends (prefixWord ++ tailWord_744410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744421 : List Nat := [1, 3, 1, 6, 2, 1, 1, 3, 1, 1, 3]
def baseStart_744421 : Nat := 118140960795 + 744421 * 2 ^ 59
def prefixEnd_744421 : Nat := 4983230072969 + 3 ^ 40 * 744421 * 2
def baseEnd_744421 : Nat := 382245782300737183113977

theorem tailTrace_744421 : CollatzResearch.WordTrace tailWord_744421 prefixEnd_744421 382245782300737183113977 := by
  unfold tailWord_744421
  simp only [CollatzResearch.WordTrace]
  refine ⟨27151264436097328830017117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18100842957398219220011411 27151264436097328830017117)
  ·
    refine ⟨10181724163536498311256419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27151264436097328830017117 10181724163536498311256419)
    ·
      refine ⟨15272586245304747466884629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10181724163536498311256419 15272586245304747466884629)
      ·
        refine ⟨715902480248660037510217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15272586245304747466884629 715902480248660037510217)
        ·
          refine ⟨536926860186495028132663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715902480248660037510217 536926860186495028132663)
          ·
            refine ⟨805390290279742542198995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536926860186495028132663 805390290279742542198995)
            ·
              refine ⟨1208085435419613813298493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805390290279742542198995 1208085435419613813298493)
              ·
                refine ⟨453032038282355179986935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1208085435419613813298493 453032038282355179986935)
                ·
                  refine ⟨679548057423532769980403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453032038282355179986935 679548057423532769980403)
                  ·
                    refine ⟨1019322086135299154970605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679548057423532769980403 1019322086135299154970605)
                    ·
                      refine ⟨382245782300737183113977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1019322086135299154970605 382245782300737183113977)
                      ·
                        rfl

theorem cell23_744421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_744421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744421 prefixEnd_744421 := by exact prefixLift 744421
  have htrace : WordTrace (prefixWord ++ tailWord_744421) baseStart_744421 baseEnd_744421 := by
    simpa [prefixWord, tailWord_744421, baseEnd_744421] using wordTrace_append hprefix tailTrace_744421
  have hstable : (prefixWord ++ tailWord_744421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744421).length < 2 ^ (prefixWord ++ tailWord_744421).sum := by decide
  have hdescent : baseEnd_744421 < baseStart_744421 := by decide
  rcases family_descends (prefixWord ++ tailWord_744421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744443 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 3]
def baseStart_744443 : Nat := 118140960795 + 744443 * 2 ^ 59
def prefixEnd_744443 : Nat := 4983230072969 + 3 ^ 40 * 744443 * 2
def baseEnd_744443 : Nat := 382257078875136097038875

theorem tailTrace_744443 : CollatzResearch.WordTrace tailWord_744443 prefixEnd_744443 382257078875136097038875 := by
  unfold tailWord_744443
  simp only [CollatzResearch.WordTrace]
  refine ⟨27152066842017626587317983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18101377894678417724878655 27152066842017626587317983)
  ·
    refine ⟨40728100263026439880976975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27152066842017626587317983 40728100263026439880976975)
    ·
      refine ⟨61092150394539659821465463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40728100263026439880976975 61092150394539659821465463)
      ·
        refine ⟨91638225591809489732198195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61092150394539659821465463 91638225591809489732198195)
        ·
          refine ⟨137457338387714234598297293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91638225591809489732198195 137457338387714234598297293)
          ·
            refine ⟨51546501895392837974361485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137457338387714234598297293 51546501895392837974361485)
            ·
              refine ⟨19329938210772314240385557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51546501895392837974361485 19329938210772314240385557)
              ·
                refine ⟨906090853629952230018073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19329938210772314240385557 906090853629952230018073)
                ·
                  refine ⟨679568140222464172513555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 906090853629952230018073 679568140222464172513555)
                  ·
                    refine ⟨1019352210333696258770333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679568140222464172513555 1019352210333696258770333)
                    ·
                      refine ⟨382257078875136097038875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1019352210333696258770333 382257078875136097038875)
                      ·
                        rfl

theorem cell23_744443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 1, 3].length) (baseStart_744443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744443 prefixEnd_744443 := by exact prefixLift 744443
  have htrace : WordTrace (prefixWord ++ tailWord_744443) baseStart_744443 baseEnd_744443 := by
    simpa [prefixWord, tailWord_744443, baseEnd_744443] using wordTrace_append hprefix tailTrace_744443
  have hstable : (prefixWord ++ tailWord_744443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744443).length < 2 ^ (prefixWord ++ tailWord_744443).sum := by decide
  have hdescent : baseEnd_744443 < baseStart_744443 := by decide
  rcases family_descends (prefixWord ++ tailWord_744443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744444 : List Nat := [2, 2, 2, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_744444 : Nat := 118140960795 + 744444 * 2 ^ 59
def prefixEnd_744444 : Nat := 4983230072969 + 3 ^ 40 * 744444 * 2
def baseEnd_744444 : Nat := 382257592355790593126371

theorem tailTrace_744444 : CollatzResearch.WordTrace tailWord_744444 prefixEnd_744444 382257592355790593126371 := by
  unfold tailWord_744444
  simp only [CollatzResearch.WordTrace]
  refine ⟨13576051657507001879052193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18101402210009335838736257 13576051657507001879052193)
  ·
    refine ⟨10182038743130251409289145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13576051657507001879052193 10182038743130251409289145)
    ·
      refine ⟨7636529057347688556966859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10182038743130251409289145 7636529057347688556966859)
      ·
        refine ⟨11454793586021532835450289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7636529057347688556966859 11454793586021532835450289)
        ·
          refine ⟨8591095189516149626587717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11454793586021532835450289 8591095189516149626587717)
          ·
            refine ⟨1610830348034278054985197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8591095189516149626587717 1610830348034278054985197)
            ·
              refine ⟨604061380512854270619449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1610830348034278054985197 604061380512854270619449)
              ·
                refine ⟨453046035384640702964587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604061380512854270619449 453046035384640702964587)
                ·
                  refine ⟨679569053076961054446881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453046035384640702964587 679569053076961054446881)
                  ·
                    refine ⟨509676789807720790835161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 679569053076961054446881 509676789807720790835161)
                    ·
                      refine ⟨382257592355790593126371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509676789807720790835161 382257592355790593126371)
                      ·
                        rfl

theorem cell23_744444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_744444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744444 prefixEnd_744444 := by exact prefixLift 744444
  have htrace : WordTrace (prefixWord ++ tailWord_744444) baseStart_744444 baseEnd_744444 := by
    simpa [prefixWord, tailWord_744444, baseEnd_744444] using wordTrace_append hprefix tailTrace_744444
  have hstable : (prefixWord ++ tailWord_744444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744444).length < 2 ^ (prefixWord ++ tailWord_744444).sum := by decide
  have hdescent : baseEnd_744444 < baseStart_744444 := by decide
  rcases family_descends (prefixWord ++ tailWord_744444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744450 : List Nat := [3, 4, 1, 3, 1, 1, 2, 8]
def baseStart_744450 : Nat := 118140960795 + 744450 * 2 ^ 59
def prefixEnd_744450 : Nat := 4983230072969 + 3 ^ 40 * 744450 * 2
def baseEnd_744450 : Nat := 14157802712582132209309

theorem tailTrace_744450 : CollatzResearch.WordTrace tailWord_744450 prefixEnd_744450 14157802712582132209309 := by
  unfold tailWord_744450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6788080538248066695705701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18101548101994844521881869 6788080538248066695705701)
  ·
    refine ⟨1272765100921512505444819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6788080538248066695705701 1272765100921512505444819)
    ·
      refine ⟨1909147651382268758167229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1272765100921512505444819 1909147651382268758167229)
      ·
        refine ⟨715930369268350784312711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1909147651382268758167229 715930369268350784312711)
        ·
          refine ⟨1073895553902526176469067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715930369268350784312711 1073895553902526176469067)
          ·
            refine ⟨1610843330853789264703601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073895553902526176469067 1610843330853789264703601)
            ·
              refine ⟨1208132498140341948527701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1610843330853789264703601 1208132498140341948527701)
              ·
                refine ⟨14157802712582132209309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1208132498140341948527701 14157802712582132209309)
                ·
                  rfl

theorem cell23_744450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 8].length) (baseStart_744450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744450 prefixEnd_744450 := by exact prefixLift 744450
  have htrace : WordTrace (prefixWord ++ tailWord_744450) baseStart_744450 baseEnd_744450 := by
    simpa [prefixWord, tailWord_744450, baseEnd_744450] using wordTrace_append hprefix tailTrace_744450
  have hstable : (prefixWord ++ tailWord_744450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744450).length < 2 ^ (prefixWord ++ tailWord_744450).sum := by decide
  have hdescent : baseEnd_744450 < baseStart_744450 := by decide
  rcases family_descends (prefixWord ++ tailWord_744450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744453 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 3, 3, 2]
def baseStart_744453 : Nat := 118140960795 + 744453 * 2 ^ 59
def prefixEnd_744453 : Nat := 4983230072969 + 3 ^ 40 * 744453 * 2
def baseEnd_744453 : Nat := 382262213681681057913829

theorem tailTrace_744453 : CollatzResearch.WordTrace tailWord_744453 prefixEnd_744453 382262213681681057913829 := by
  unfold tailWord_744453
  simp only [CollatzResearch.WordTrace]
  refine ⟨27152431571981398295182013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18101621047987598863454675 27152431571981398295182013)
  ·
    refine ⟨10182161839493024360693255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27152431571981398295182013 10182161839493024360693255)
    ·
      refine ⟨15273242759239536541039883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10182161839493024360693255 15273242759239536541039883)
      ·
        refine ⟨22909864138859304811559825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15273242759239536541039883 22909864138859304811559825)
        ·
          refine ⟨17182398104144478608669869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22909864138859304811559825 17182398104144478608669869)
          ·
            refine ⟨6443399289054179478251201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17182398104144478608669869 6443399289054179478251201)
            ·
              refine ⟨4832549466790634608688401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443399289054179478251201 4832549466790634608688401)
              ·
                refine ⟨3624412100092975956516301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4832549466790634608688401 3624412100092975956516301)
                ·
                  refine ⟨1359154537534865983693613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3624412100092975956516301 1359154537534865983693613)
                  ·
                    refine ⟨509682951575574743885105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1359154537534865983693613 509682951575574743885105)
                    ·
                      refine ⟨382262213681681057913829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509682951575574743885105 382262213681681057913829)
                      ·
                        rfl

theorem cell23_744453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_744453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744453 prefixEnd_744453 := by exact prefixLift 744453
  have htrace : WordTrace (prefixWord ++ tailWord_744453) baseStart_744453 baseEnd_744453 := by
    simpa [prefixWord, tailWord_744453, baseEnd_744453] using wordTrace_append hprefix tailTrace_744453
  have hstable : (prefixWord ++ tailWord_744453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744453).length < 2 ^ (prefixWord ++ tailWord_744453).sum := by decide
  have hdescent : baseEnd_744453 < baseStart_744453 := by decide
  rcases family_descends (prefixWord ++ tailWord_744453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744460 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_744460 : Nat := 118140960795 + 744460 * 2 ^ 59
def prefixEnd_744460 : Nat := 4983230072969 + 3 ^ 40 * 744460 * 2
def baseEnd_744460 : Nat := 382265808046262530526297

theorem tailTrace_744460 : CollatzResearch.WordTrace tailWord_744460 prefixEnd_744460 382265808046262530526297 := by
  unfold tailWord_744460
  simp only [CollatzResearch.WordTrace]
  refine ⟨13576343441478019245343417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18101791255304025660457889 13576343441478019245343417)
  ·
    refine ⟨10182257581108514434007563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13576343441478019245343417 10182257581108514434007563)
    ·
      refine ⟨15273386371662771651011345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10182257581108514434007563 15273386371662771651011345)
      ·
        refine ⟨11455039778747078738258509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15273386371662771651011345 11455039778747078738258509)
        ·
          refine ⟨4295639917030154526846941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11455039778747078738258509 4295639917030154526846941)
          ·
            refine ⟨1610864968886307947567603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4295639917030154526846941 1610864968886307947567603)
            ·
              refine ⟨2416297453329461921351405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610864968886307947567603 2416297453329461921351405)
              ·
                refine ⟨906111544998548220506777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2416297453329461921351405 906111544998548220506777)
                ·
                  refine ⟨679583658748911165380083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 906111544998548220506777 679583658748911165380083)
                  ·
                    refine ⟨1019375488123366748070125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679583658748911165380083 1019375488123366748070125)
                    ·
                      refine ⟨382265808046262530526297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1019375488123366748070125 382265808046262530526297)
                      ·
                        rfl

theorem cell23_744460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_744460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744460 prefixEnd_744460 := by exact prefixLift 744460
  have htrace : WordTrace (prefixWord ++ tailWord_744460) baseStart_744460 baseEnd_744460 := by
    simpa [prefixWord, tailWord_744460, baseEnd_744460] using wordTrace_append hprefix tailTrace_744460
  have hstable : (prefixWord ++ tailWord_744460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744460).length < 2 ^ (prefixWord ++ tailWord_744460).sum := by decide
  have hdescent : baseEnd_744460 < baseStart_744460 := by decide
  rcases family_descends (prefixWord ++ tailWord_744460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744483 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 3, 4, 2]
def baseStart_744483 : Nat := 118140960795 + 744483 * 2 ^ 59
def prefixEnd_744483 : Nat := 4983230072969 + 3 ^ 40 * 744483 * 2
def baseEnd_744483 : Nat := 382277618101315940538691

theorem tailTrace_744483 : CollatzResearch.WordTrace tailWord_744483 prefixEnd_744483 382277618101315940538691 := by
  unfold tailWord_744483
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153525761872713418774103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18102350507915142279182735 27153525761872713418774103)
  ·
    refine ⟨40730288642809070128161155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27153525761872713418774103 40730288642809070128161155)
    ·
      refine ⟨61095432964213605192241733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40730288642809070128161155 61095432964213605192241733)
      ·
        refine ⟨11455393680790050973545325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61095432964213605192241733 11455393680790050973545325)
        ·
          refine ⟨4295772630296269115079497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11455393680790050973545325 4295772630296269115079497)
          ·
            refine ⟨3221829472722201836309623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4295772630296269115079497 3221829472722201836309623)
            ·
              refine ⟨4832744209083302754464435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221829472722201836309623 4832744209083302754464435)
              ·
                refine ⟨7249116313624954131696653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832744209083302754464435 7249116313624954131696653)
                ·
                  refine ⟨2718418617609357799386245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7249116313624954131696653 2718418617609357799386245)
                  ·
                    refine ⟨509703490801754587384921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2718418617609357799386245 509703490801754587384921)
                    ·
                      refine ⟨382277618101315940538691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509703490801754587384921 382277618101315940538691)
                      ·
                        rfl

theorem cell23_744483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_744483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744483 prefixEnd_744483 := by exact prefixLift 744483
  have htrace : WordTrace (prefixWord ++ tailWord_744483) baseStart_744483 baseEnd_744483 := by
    simpa [prefixWord, tailWord_744483, baseEnd_744483] using wordTrace_append hprefix tailTrace_744483
  have hstable : (prefixWord ++ tailWord_744483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744483).length < 2 ^ (prefixWord ++ tailWord_744483).sum := by decide
  have hdescent : baseEnd_744483 < baseStart_744483 := by decide
  rcases family_descends (prefixWord ++ tailWord_744483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744496 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_744496 : Nat := 118140960795 + 744496 * 2 ^ 59
def prefixEnd_744496 : Nat := 4983230072969 + 3 ^ 40 * 744496 * 2
def baseEnd_744496 : Nat := 382284293349824389676131

theorem tailTrace_744496 : CollatzResearch.WordTrace tailWord_744496 prefixEnd_744496 382284293349824389676131 := by
  unfold tailWord_744496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13576999955412808319498671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18102666607217077759331561 13576999955412808319498671)
  ·
    refine ⟨20365499933119212479248007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13576999955412808319498671 20365499933119212479248007)
    ·
      refine ⟨30548249899678818718872011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20365499933119212479248007 30548249899678818718872011)
      ·
        refine ⟨45822374849518228078308017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30548249899678818718872011 45822374849518228078308017)
        ·
          refine ⟨34366781137138671058731013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45822374849518228078308017 34366781137138671058731013)
          ·
            refine ⟨6443771463213500823512065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34366781137138671058731013 6443771463213500823512065)
            ·
              refine ⟨4832828597410125617634049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443771463213500823512065 4832828597410125617634049)
              ·
                refine ⟨3624621448057594213225537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4832828597410125617634049 3624621448057594213225537)
                ·
                  refine ⟨2718466086043195659919153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3624621448057594213225537 2718466086043195659919153)
                  ·
                    refine ⟨2038849564532396744939365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2718466086043195659919153 2038849564532396744939365)
                    ·
                      refine ⟨382284293349824389676131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2038849564532396744939365 382284293349824389676131)
                      ·
                        rfl

theorem cell23_744496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_744496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744496 prefixEnd_744496 := by exact prefixLift 744496
  have htrace : WordTrace (prefixWord ++ tailWord_744496) baseStart_744496 baseEnd_744496 := by
    simpa [prefixWord, tailWord_744496, baseEnd_744496] using wordTrace_append hprefix tailTrace_744496
  have hstable : (prefixWord ++ tailWord_744496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744496).length < 2 ^ (prefixWord ++ tailWord_744496).sum := by decide
  have hdescent : baseEnd_744496 < baseStart_744496 := by decide
  rcases family_descends (prefixWord ++ tailWord_744496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744536 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 1, 7]
def baseStart_744536 : Nat := 118140960795 + 744536 * 2 ^ 59
def prefixEnd_744536 : Nat := 4983230072969 + 3 ^ 40 * 744536 * 2
def baseEnd_744536 : Nat := 127434944192001411058649

theorem tailTrace_744536 : CollatzResearch.WordTrace tailWord_744536 prefixEnd_744536 127434944192001411058649 := by
  unfold tailWord_744536
  simp only [CollatzResearch.WordTrace]
  refine ⟨13577729415340351735226731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18103639220453802313635641 13577729415340351735226731)
  ·
    refine ⟨20366594123010527602840097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13577729415340351735226731 20366594123010527602840097)
    ·
      refine ⟨15274945592257895702130073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20366594123010527602840097 15274945592257895702130073)
      ·
        refine ⟨11456209194193421776597555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15274945592257895702130073 11456209194193421776597555)
        ·
          refine ⟨17184313791290132664896333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11456209194193421776597555 17184313791290132664896333)
          ·
            refine ⟨6444117671733799749336125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17184313791290132664896333 6444117671733799749336125)
            ·
              refine ⟨2416544126900174906001047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6444117671733799749336125 2416544126900174906001047)
              ·
                refine ⟨3624816190350262359001571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416544126900174906001047 3624816190350262359001571)
                ·
                  refine ⟨5437224285525393538502357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3624816190350262359001571 5437224285525393538502357)
                  ·
                    refine ⟨127434944192001411058649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5437224285525393538502357 127434944192001411058649)
                    ·
                      rfl

theorem cell23_744536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_744536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744536 prefixEnd_744536 := by exact prefixLift 744536
  have htrace : WordTrace (prefixWord ++ tailWord_744536) baseStart_744536 baseEnd_744536 := by
    simpa [prefixWord, tailWord_744536, baseEnd_744536] using wordTrace_append hprefix tailTrace_744536
  have hstable : (prefixWord ++ tailWord_744536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744536).length < 2 ^ (prefixWord ++ tailWord_744536).sum := by decide
  have hdescent : baseEnd_744536 < baseStart_744536 := by decide
  rcases family_descends (prefixWord ++ tailWord_744536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744540 : List Nat := [2, 2, 4, 1, 1, 1, 4, 3, 5]
def baseStart_744540 : Nat := 118140960795 + 744540 * 2 ^ 59
def prefixEnd_744540 : Nat := 4983230072969 + 3 ^ 40 * 744540 * 2
def baseEnd_744540 : Nat := 42478542944291357502881

theorem tailTrace_744540 : CollatzResearch.WordTrace tailWord_744540 prefixEnd_744540 42478542944291357502881 := by
  unfold tailWord_744540
  simp only [CollatzResearch.WordTrace]
  refine ⟨13577802361333106076799537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18103736481777474769066049 13577802361333106076799537)
  ·
    refine ⟨10183351770999829557599653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13577802361333106076799537 10183351770999829557599653)
    ·
      refine ⟨1909378457062468042049935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10183351770999829557599653 1909378457062468042049935)
      ·
        refine ⟨2864067685593702063074903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1909378457062468042049935 2864067685593702063074903)
        ·
          refine ⟨4296101528390553094612355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2864067685593702063074903 4296101528390553094612355)
          ·
            refine ⟨6444152292585829641918533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296101528390553094612355 6444152292585829641918533)
            ·
              refine ⟨1208278554859843057859725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6444152292585829641918533 1208278554859843057859725)
              ·
                refine ⟨453104458072441146697397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1208278554859843057859725 453104458072441146697397)
                ·
                  refine ⟨42478542944291357502881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 453104458072441146697397 42478542944291357502881)
                  ·
                    rfl

theorem cell23_744540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_744540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744540 prefixEnd_744540 := by exact prefixLift 744540
  have htrace : WordTrace (prefixWord ++ tailWord_744540) baseStart_744540 baseEnd_744540 := by
    simpa [prefixWord, tailWord_744540, baseEnd_744540] using wordTrace_append hprefix tailTrace_744540
  have hstable : (prefixWord ++ tailWord_744540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744540).length < 2 ^ (prefixWord ++ tailWord_744540).sum := by decide
  have hdescent : baseEnd_744540 < baseStart_744540 := by decide
  rcases family_descends (prefixWord ++ tailWord_744540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744643 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 1, 5]
def baseStart_744643 : Nat := 118140960795 + 744643 * 2 ^ 59
def prefixEnd_744643 : Nat := 4983230072969 + 3 ^ 40 * 744643 * 2
def baseEnd_744643 : Nat := 127453258335345104845985

theorem tailTrace_744643 : CollatzResearch.WordTrace tailWord_744643 prefixEnd_744643 127453258335345104845985 := by
  unfold tailWord_744643
  simp only [CollatzResearch.WordTrace]
  refine ⟨27159361441293060744598583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18106240960862040496399055 27159361441293060744598583)
  ·
    refine ⟨40739042161939591116897875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27159361441293060744598583 40739042161939591116897875)
    ·
      refine ⟨61108563242909386675346813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40739042161939591116897875 61108563242909386675346813)
      ·
        refine ⟨22915711216091020003255055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61108563242909386675346813 22915711216091020003255055)
        ·
          refine ⟨34373566824136530004882583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22915711216091020003255055 34373566824136530004882583)
          ·
            refine ⟨51560350236204795007323875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34373566824136530004882583 51560350236204795007323875)
            ·
              refine ⟨77340525354307192510985813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51560350236204795007323875 77340525354307192510985813)
              ·
                refine ⟨906334281495787412238115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 77340525354307192510985813 906334281495787412238115)
                ·
                  refine ⟨1359501422243681118357173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906334281495787412238115 1359501422243681118357173)
                  ·
                    refine ⟨127453258335345104845985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1359501422243681118357173 127453258335345104845985)
                    ·
                      rfl

theorem cell23_744643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 5].length) (baseStart_744643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744643 prefixEnd_744643 := by exact prefixLift 744643
  have htrace : WordTrace (prefixWord ++ tailWord_744643) baseStart_744643 baseEnd_744643 := by
    simpa [prefixWord, tailWord_744643, baseEnd_744643] using wordTrace_append hprefix tailTrace_744643
  have hstable : (prefixWord ++ tailWord_744643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744643).length < 2 ^ (prefixWord ++ tailWord_744643).sum := by decide
  have hdescent : baseEnd_744643 < baseStart_744643 := by decide
  rcases family_descends (prefixWord ++ tailWord_744643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744657 : List Nat := [1, 2, 2, 1, 2, 2, 1, 7, 1, 1, 3]
def baseStart_744657 : Nat := 118140960795 + 744657 * 2 ^ 59
def prefixEnd_744657 : Nat := 4983230072969 + 3 ^ 40 * 744657 * 2
def baseEnd_744657 : Nat := 382366963735198259762891

theorem tailTrace_744657 : CollatzResearch.WordTrace tailWord_744657 prefixEnd_744657 382366963735198259762891 := by
  unfold tailWord_744657
  simp only [CollatzResearch.WordTrace]
  refine ⟨27159872063242341135608225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18106581375494894090405483 27159872063242341135608225)
  ·
    refine ⟨20369904047431755851706169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27159872063242341135608225 20369904047431755851706169)
    ·
      refine ⟨15277428035573816888779627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20369904047431755851706169 15277428035573816888779627)
      ·
        refine ⟨22916142053360725333169441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15277428035573816888779627 22916142053360725333169441)
        ·
          refine ⟨17187106540020543999877081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22916142053360725333169441 17187106540020543999877081)
          ·
            refine ⟨12890329905015407999907811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17187106540020543999877081 12890329905015407999907811)
            ·
              refine ⟨19335494857523111999861717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12890329905015407999907811 19335494857523111999861717)
              ·
                refine ⟨453175660723197937496759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19335494857523111999861717 453175660723197937496759)
                ·
                  refine ⟨679763491084796906245139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453175660723197937496759 679763491084796906245139)
                  ·
                    refine ⟨1019645236627195359367709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679763491084796906245139 1019645236627195359367709)
                    ·
                      refine ⟨382366963735198259762891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1019645236627195359367709 382366963735198259762891)
                      ·
                        rfl

theorem cell23_744657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_744657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744657 prefixEnd_744657 := by exact prefixLift 744657
  have htrace : WordTrace (prefixWord ++ tailWord_744657) baseStart_744657 baseEnd_744657 := by
    simpa [prefixWord, tailWord_744657, baseEnd_744657] using wordTrace_append hprefix tailTrace_744657
  have hstable : (prefixWord ++ tailWord_744657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744657).length < 2 ^ (prefixWord ++ tailWord_744657).sum := by decide
  have hdescent : baseEnd_744657 < baseStart_744657 := by decide
  rcases family_descends (prefixWord ++ tailWord_744657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744697 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 3, 2, 2]
def baseStart_744697 : Nat := 118140960795 + 744697 * 2 ^ 59
def prefixEnd_744697 : Nat := 4983230072969 + 3 ^ 40 * 744697 * 2
def baseEnd_744697 : Nat := 382387502961378103262707

theorem tailTrace_744697 : CollatzResearch.WordTrace tailWord_744697 prefixEnd_744697 382387502961378103262707 := by
  unfold tailWord_744697
  simp only [CollatzResearch.WordTrace]
  refine ⟨27161330983097427967064345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18107553988731618644709563 27161330983097427967064345)
  ·
    refine ⟨20370998237323070975298259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27161330983097427967064345 20370998237323070975298259)
    ·
      refine ⟨30556497355984606462947389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20370998237323070975298259 30556497355984606462947389)
      ·
        refine ⟨11458686508494227423605271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30556497355984606462947389 11458686508494227423605271)
        ·
          refine ⟨17188029762741341135407907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11458686508494227423605271 17188029762741341135407907)
          ·
            refine ⟨25782044644112011703111861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17188029762741341135407907 25782044644112011703111861)
            ·
              refine ⟨2417066685385501097166737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25782044644112011703111861 2417066685385501097166737)
              ·
                refine ⟨1812800014039125822875053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417066685385501097166737 1812800014039125822875053)
                ·
                  refine ⟨679800005264672183578145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1812800014039125822875053 679800005264672183578145)
                  ·
                    refine ⟨509850003948504137683609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 679800005264672183578145 509850003948504137683609)
                    ·
                      refine ⟨382387502961378103262707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509850003948504137683609 382387502961378103262707)
                      ·
                        rfl

theorem cell23_744697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_744697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744697 prefixEnd_744697 := by exact prefixLift 744697
  have htrace : WordTrace (prefixWord ++ tailWord_744697) baseStart_744697 baseEnd_744697 := by
    simpa [prefixWord, tailWord_744697, baseEnd_744697] using wordTrace_append hprefix tailTrace_744697
  have hstable : (prefixWord ++ tailWord_744697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744697).length < 2 ^ (prefixWord ++ tailWord_744697).sum := by decide
  have hdescent : baseEnd_744697 < baseStart_744697 := by decide
  rcases family_descends (prefixWord ++ tailWord_744697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744734 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_744734 : Nat := 118140960795 + 744734 * 2 ^ 59
def prefixEnd_744734 : Nat := 4983230072969 + 3 ^ 40 * 744734 * 2
def baseEnd_744734 : Nat := 382406501745594458500037

theorem tailTrace_744734 : CollatzResearch.WordTrace tailWord_744734 prefixEnd_744734 382406501745594458500037 := by
  unfold tailWord_744734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3395335060495422910770157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18108453655975588857440837 3395335060495422910770157)
  ·
    refine ⟨1273250647685783591538809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3395335060495422910770157 1273250647685783591538809)
    ·
      refine ⟨954937985764337693654107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1273250647685783591538809 954937985764337693654107)
      ·
        refine ⟨1432406978646506540481161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954937985764337693654107 1432406978646506540481161)
        ·
          refine ⟨1074305233984879905360871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1432406978646506540481161 1074305233984879905360871)
          ·
            refine ⟨1611457850977319858041307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074305233984879905360871 1611457850977319858041307)
            ·
              refine ⟨2417186776465979787061961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611457850977319858041307 2417186776465979787061961)
              ·
                refine ⟨1812890082349484840296471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417186776465979787061961 1812890082349484840296471)
                ·
                  refine ⟨2719335123524227260444707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812890082349484840296471 2719335123524227260444707)
                  ·
                    refine ⟨4079002685286340890667061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2719335123524227260444707 4079002685286340890667061)
                    ·
                      refine ⟨382406501745594458500037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4079002685286340890667061 382406501745594458500037)
                      ·
                        rfl

theorem cell23_744734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_744734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744734 prefixEnd_744734 := by exact prefixLift 744734
  have htrace : WordTrace (prefixWord ++ tailWord_744734) baseStart_744734 baseEnd_744734 := by
    simpa [prefixWord, tailWord_744734, baseEnd_744734] using wordTrace_append hprefix tailTrace_744734
  have hstable : (prefixWord ++ tailWord_744734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744734).length < 2 ^ (prefixWord ++ tailWord_744734).sum := by decide
  have hdescent : baseEnd_744734 < baseStart_744734 := by decide
  rcases family_descends (prefixWord ++ tailWord_744734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744765 : List Nat := [1, 4, 1, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_744765 : Nat := 118140960795 + 744765 * 2 ^ 59
def prefixEnd_744765 : Nat := 4983230072969 + 3 ^ 40 * 744765 * 2
def baseEnd_744765 : Nat := 382422419645883837212395

theorem tailTrace_744765 : CollatzResearch.WordTrace tailWord_744765 prefixEnd_744765 382422419645883837212395 := by
  unfold tailWord_744765
  simp only [CollatzResearch.WordTrace]
  refine ⟨27163811146851075580539749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18109207431234050387026499 27163811146851075580539749)
  ·
    refine ⟨5093214590034576671351203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27163811146851075580539749 5093214590034576671351203)
    ·
      refine ⟨7639821885051865007026805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5093214590034576671351203 7639821885051865007026805)
      ·
        refine ⟨716233301723612344408763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7639821885051865007026805 716233301723612344408763)
        ·
          refine ⟨1074349952585418516613145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716233301723612344408763 1074349952585418516613145)
          ·
            refine ⟨805762464439063887459859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074349952585418516613145 805762464439063887459859)
            ·
              refine ⟨1208643696658595831189789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805762464439063887459859 1208643696658595831189789)
              ·
                refine ⟨453241386246973436696171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1208643696658595831189789 453241386246973436696171)
                ·
                  refine ⟨679862079370460155044257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453241386246973436696171 679862079370460155044257)
                  ·
                    refine ⟨509896559527845116283193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 679862079370460155044257 509896559527845116283193)
                    ·
                      refine ⟨382422419645883837212395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509896559527845116283193 382422419645883837212395)
                      ·
                        rfl

theorem cell23_744765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_744765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744765 prefixEnd_744765 := by exact prefixLift 744765
  have htrace : WordTrace (prefixWord ++ tailWord_744765) baseStart_744765 baseEnd_744765 := by
    simpa [prefixWord, tailWord_744765, baseEnd_744765] using wordTrace_append hprefix tailTrace_744765
  have hstable : (prefixWord ++ tailWord_744765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744765).length < 2 ^ (prefixWord ++ tailWord_744765).sum := by decide
  have hdescent : baseEnd_744765 < baseStart_744765 := by decide
  rcases family_descends (prefixWord ++ tailWord_744765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744787 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 4, 2, 2]
def baseStart_744787 : Nat := 118140960795 + 744787 * 2 ^ 59
def prefixEnd_744787 : Nat := 4983230072969 + 3 ^ 40 * 744787 * 2
def baseEnd_744787 : Nat := 382433716220282751137293

theorem tailTrace_744787 : CollatzResearch.WordTrace tailWord_744787 prefixEnd_744787 382433716220282751137293 := by
  unfold tailWord_744787
  simp only [CollatzResearch.WordTrace]
  refine ⟨27164613552771373337840615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18109742368514248891893743 27164613552771373337840615)
  ·
    refine ⟨40746920329157060006760923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27164613552771373337840615 40746920329157060006760923)
    ·
      refine ⟨61120380493735590010141385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40746920329157060006760923 61120380493735590010141385)
      ·
        refine ⟨45840285370301692507606039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61120380493735590010141385 45840285370301692507606039)
        ·
          refine ⟨68760428055452538761409059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45840285370301692507606039 68760428055452538761409059)
          ·
            refine ⟨103140642083178808142113589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68760428055452538761409059 103140642083178808142113589)
            ·
              refine ⟨9669435195298013263323149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103140642083178808142113589 9669435195298013263323149)
              ·
                refine ⟨3626038198236754973746181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9669435195298013263323149 3626038198236754973746181)
                ·
                  refine ⟨679882162169391557577409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3626038198236754973746181 679882162169391557577409)
                  ·
                    refine ⟨509911621627043668183057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 679882162169391557577409 509911621627043668183057)
                    ·
                      refine ⟨382433716220282751137293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509911621627043668183057 382433716220282751137293)
                      ·
                        rfl

theorem cell23_744787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 2, 2].length) (baseStart_744787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744787 prefixEnd_744787 := by exact prefixLift 744787
  have htrace : WordTrace (prefixWord ++ tailWord_744787) baseStart_744787 baseEnd_744787 := by
    simpa [prefixWord, tailWord_744787, baseEnd_744787] using wordTrace_append hprefix tailTrace_744787
  have hstable : (prefixWord ++ tailWord_744787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744787).length < 2 ^ (prefixWord ++ tailWord_744787).sum := by decide
  have hdescent : baseEnd_744787 < baseStart_744787 := by decide
  rcases family_descends (prefixWord ++ tailWord_744787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744808 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_744808 : Nat := 118140960795 + 744808 * 2 ^ 59
def prefixEnd_744808 : Nat := 4983230072969 + 3 ^ 40 * 744808 * 2
def baseEnd_744808 : Nat := 382444499314027168974697

theorem tailTrace_744808 : CollatzResearch.WordTrace tailWord_744808 prefixEnd_744808 382444499314027168974697 := by
  unfold tailWord_744808
  simp only [CollatzResearch.WordTrace]
  refine ⟨13582689742847646962177539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18110252990463529282903385 13582689742847646962177539)
  ·
    refine ⟨20374034614271470443266309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13582689742847646962177539 20374034614271470443266309)
    ·
      refine ⟨3820131490175900708112433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20374034614271470443266309 3820131490175900708112433)
      ·
        refine ⟨2865098617631925531084325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3820131490175900708112433 2865098617631925531084325)
        ·
          refine ⟨537205990805986037078311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2865098617631925531084325 537205990805986037078311)
          ·
            refine ⟨805808986208979055617467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537205990805986037078311 805808986208979055617467)
            ·
              refine ⟨1208713479313468583426201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805808986208979055617467 1208713479313468583426201)
              ·
                refine ⟨906535109485101437569651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208713479313468583426201 906535109485101437569651)
                ·
                  refine ⟨1359802664227652156354477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906535109485101437569651 1359802664227652156354477)
                  ·
                    refine ⟨509925999085369558632929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1359802664227652156354477 509925999085369558632929)
                    ·
                      refine ⟨382444499314027168974697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 509925999085369558632929 382444499314027168974697)
                      ·
                        rfl

theorem cell23_744808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_744808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744808 prefixEnd_744808 := by exact prefixLift 744808
  have htrace : WordTrace (prefixWord ++ tailWord_744808) baseStart_744808 baseEnd_744808 := by
    simpa [prefixWord, tailWord_744808, baseEnd_744808] using wordTrace_append hprefix tailTrace_744808
  have hstable : (prefixWord ++ tailWord_744808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744808).length < 2 ^ (prefixWord ++ tailWord_744808).sum := by decide
  have hdescent : baseEnd_744808 < baseStart_744808 := by decide
  rcases family_descends (prefixWord ++ tailWord_744808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744904 : List Nat := [2, 1, 3, 1, 3, 1, 1, 6, 1, 4]
def baseStart_744904 : Nat := 118140960795 + 744904 * 2 ^ 59
def prefixEnd_744904 : Nat := 4983230072969 + 3 ^ 40 * 744904 * 2
def baseEnd_744904 : Nat := 127497931152286264458085

theorem tailTrace_744904 : CollatzResearch.WordTrace tailWord_744904 prefixEnd_744904 127497931152286264458085 := by
  unfold tailWord_744904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13584440446673751159924883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18112587262231668213233177 13584440446673751159924883)
  ·
    refine ⟨20376660670010626739887325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13584440446673751159924883 20376660670010626739887325)
    ·
      refine ⟨7641247751253985027457747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20376660670010626739887325 7641247751253985027457747)
      ·
        refine ⟨11461871626880977541186621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641247751253985027457747 11461871626880977541186621)
        ·
          refine ⟨4298201860080366577944983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11461871626880977541186621 4298201860080366577944983)
          ·
            refine ⟨6447302790120549866917475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298201860080366577944983 6447302790120549866917475)
            ·
              refine ⟨9670954185180824800376213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447302790120549866917475 9670954185180824800376213)
              ·
                refine ⟨453325977430351162517635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9670954185180824800376213 453325977430351162517635)
                ·
                  refine ⟨679988966145526743776453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453325977430351162517635 679988966145526743776453)
                  ·
                    refine ⟨127497931152286264458085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 679988966145526743776453 127497931152286264458085)
                    ·
                      rfl

theorem cell23_744904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_744904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744904 prefixEnd_744904 := by exact prefixLift 744904
  have htrace : WordTrace (prefixWord ++ tailWord_744904) baseStart_744904 baseEnd_744904 := by
    simpa [prefixWord, tailWord_744904, baseEnd_744904] using wordTrace_append hprefix tailTrace_744904
  have hstable : (prefixWord ++ tailWord_744904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744904).length < 2 ^ (prefixWord ++ tailWord_744904).sum := by decide
  have hdescent : baseEnd_744904 < baseStart_744904 := by decide
  rcases family_descends (prefixWord ++ tailWord_744904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744938 : List Nat := [3, 1, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_744938 : Nat := 118140960795 + 744938 * 2 ^ 59
def prefixEnd_744938 : Nat := 4983230072969 + 3 ^ 40 * 744938 * 2
def baseEnd_744938 : Nat := 127503750599703886783033

theorem tailTrace_744938 : CollatzResearch.WordTrace tailWord_744938 prefixEnd_744938 127503750599703886783033 := by
  unfold tailWord_744938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792530243806081531646867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18113413983482884084391645 6792530243806081531646867)
  ·
    refine ⟨10188795365709122297470301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6792530243806081531646867 10188795365709122297470301)
    ·
      refine ⟨3820798262140920861551363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10188795365709122297470301 3820798262140920861551363)
      ·
        refine ⟨5731197393211381292327045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3820798262140920861551363 5731197393211381292327045)
        ·
          refine ⟨1074599511227133992311321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5731197393211381292327045 1074599511227133992311321)
          ·
            refine ⟨805949633420350494233491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074599511227133992311321 805949633420350494233491)
            ·
              refine ⟨1208924450130525741350237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805949633420350494233491 1208924450130525741350237)
              ·
                refine ⟨453346668798947153006339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1208924450130525741350237 453346668798947153006339)
                ·
                  refine ⟨680020003198420729509509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453346668798947153006339 680020003198420729509509)
                  ·
                    refine ⟨127503750599703886783033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 680020003198420729509509 127503750599703886783033)
                    ·
                      rfl

theorem cell23_744938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_744938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744938 prefixEnd_744938 := by exact prefixLift 744938
  have htrace : WordTrace (prefixWord ++ tailWord_744938) baseStart_744938 baseEnd_744938 := by
    simpa [prefixWord, tailWord_744938, baseEnd_744938] using wordTrace_append hprefix tailTrace_744938
  have hstable : (prefixWord ++ tailWord_744938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744938).length < 2 ^ (prefixWord ++ tailWord_744938).sum := by decide
  have hdescent : baseEnd_744938 < baseStart_744938 := by decide
  rcases family_descends (prefixWord ++ tailWord_744938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744954 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2]
def baseStart_744954 : Nat := 118140960795 + 744954 * 2 ^ 59
def prefixEnd_744954 : Nat := 4983230072969 + 3 ^ 40 * 744954 * 2
def baseEnd_744954 : Nat := 382519467489583597749025

theorem tailTrace_744954 : CollatzResearch.WordTrace tailWord_744954 prefixEnd_744954 382519467489583597749025 := by
  unfold tailWord_744954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792676135791590214792479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18113803028777573906113277 6792676135791590214792479)
  ·
    refine ⟨10189014203687385322188719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6792676135791590214792479 10189014203687385322188719)
    ·
      refine ⟨15283521305531077983283079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10189014203687385322188719 15283521305531077983283079)
      ·
        refine ⟨22925281958296616974924619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15283521305531077983283079 22925281958296616974924619)
        ·
          refine ⟨34387922937444925462386929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22925281958296616974924619 34387922937444925462386929)
          ·
            refine ⟨25790942203083694096790197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34387922937444925462386929 25790942203083694096790197)
            ·
              refine ⟨2417900831539096321574081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25790942203083694096790197 2417900831539096321574081)
              ·
                refine ⟨1813425623654322241180561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417900831539096321574081 1813425623654322241180561)
                ·
                  refine ⟨1360069217740741680885421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1813425623654322241180561 1360069217740741680885421)
                  ·
                    refine ⟨510025956652778130332033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360069217740741680885421 510025956652778130332033)
                    ·
                      refine ⟨382519467489583597749025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510025956652778130332033 382519467489583597749025)
                      ·
                        rfl

theorem cell23_744954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2].length) (baseStart_744954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744954 prefixEnd_744954 := by exact prefixLift 744954
  have htrace : WordTrace (prefixWord ++ tailWord_744954) baseStart_744954 baseEnd_744954 := by
    simpa [prefixWord, tailWord_744954, baseEnd_744954] using wordTrace_append hprefix tailTrace_744954
  have hstable : (prefixWord ++ tailWord_744954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744954).length < 2 ^ (prefixWord ++ tailWord_744954).sum := by decide
  have hdescent : baseEnd_744954 < baseStart_744954 := by decide
  rcases family_descends (prefixWord ++ tailWord_744954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744984 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_744984 : Nat := 118140960795 + 744984 * 2 ^ 59
def prefixEnd_744984 : Nat := 4983230072969 + 3 ^ 40 * 744984 * 2
def baseEnd_744984 : Nat := 382534871909218480373887

theorem tailTrace_744984 : CollatzResearch.WordTrace tailWord_744984 prefixEnd_744984 382534871909218480373887 := by
  unfold tailWord_744984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13585899366528837991381003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18114532488705117321841337 13585899366528837991381003)
  ·
    refine ⟨20378849049793256987071505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13585899366528837991381003 20378849049793256987071505)
    ·
      refine ⟨15284136787344942740303629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20378849049793256987071505 15284136787344942740303629)
      ·
        refine ⟨5731551295254353527613861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15284136787344942740303629 5731551295254353527613861)
        ·
          refine ⟨1074665867860191286427599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5731551295254353527613861 1074665867860191286427599)
          ·
            refine ⟨1611998801790286929641399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1074665867860191286427599 1611998801790286929641399)
            ·
              refine ⟨2417998202685430394462099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611998801790286929641399 2417998202685430394462099)
              ·
                refine ⟨3626997304028145591693149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417998202685430394462099 3626997304028145591693149)
                ·
                  refine ⟨1360123989010554596884931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3626997304028145591693149 1360123989010554596884931)
                  ·
                    refine ⟨2040185983515831895327397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1360123989010554596884931 2040185983515831895327397)
                    ·
                      refine ⟨382534871909218480373887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2040185983515831895327397 382534871909218480373887)
                      ·
                        rfl

theorem cell23_744984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_744984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_744984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_744984 prefixEnd_744984 := by exact prefixLift 744984
  have htrace : WordTrace (prefixWord ++ tailWord_744984) baseStart_744984 baseEnd_744984 := by
    simpa [prefixWord, tailWord_744984, baseEnd_744984] using wordTrace_append hprefix tailTrace_744984
  have hstable : (prefixWord ++ tailWord_744984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744984).length < 2 ^ (prefixWord ++ tailWord_744984).sum := by decide
  have hdescent : baseEnd_744984 < baseStart_744984 := by decide
  rcases family_descends (prefixWord ++ tailWord_744984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745018 : List Nat := [3, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2]
def baseStart_745018 : Nat := 118140960795 + 745018 * 2 ^ 59
def prefixEnd_745018 : Nat := 4983230072969 + 3 ^ 40 * 745018 * 2
def baseEnd_745018 : Nat := 382552330251471347348731

theorem tailTrace_745018 : CollatzResearch.WordTrace tailWord_745018 prefixEnd_745018 382552330251471347348731 := by
  unfold tailWord_745018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793259703733624947374927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18115359209956333192999805 6793259703733624947374927)
  ·
    refine ⟨10189889555600437421062391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6793259703733624947374927 10189889555600437421062391)
    ·
      refine ⟨15284834333400656131593587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10189889555600437421062391 15284834333400656131593587)
      ·
        refine ⟨22927251500100984197390381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15284834333400656131593587 22927251500100984197390381)
        ·
          refine ⟨8597719312537869074021393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22927251500100984197390381 8597719312537869074021393)
          ·
            refine ⟨6448289484403401805516045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8597719312537869074021393 6448289484403401805516045)
            ·
              refine ⟨2418108556651275677068517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6448289484403401805516045 2418108556651275677068517)
              ·
                refine ⟨453395354372114189450347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2418108556651275677068517 453395354372114189450347)
                ·
                  refine ⟨680093031558171284175521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453395354372114189450347 680093031558171284175521)
                  ·
                    refine ⟨510069773668628463131641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 680093031558171284175521 510069773668628463131641)
                    ·
                      refine ⟨382552330251471347348731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510069773668628463131641 382552330251471347348731)
                      ·
                        rfl

theorem cell23_745018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2].length) (baseStart_745018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745018 prefixEnd_745018 := by exact prefixLift 745018
  have htrace : WordTrace (prefixWord ++ tailWord_745018) baseStart_745018 baseEnd_745018 := by
    simpa [prefixWord, tailWord_745018, baseEnd_745018] using wordTrace_append hprefix tailTrace_745018
  have hstable : (prefixWord ++ tailWord_745018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745018).length < 2 ^ (prefixWord ++ tailWord_745018).sum := by decide
  have hdescent : baseEnd_745018 < baseStart_745018 := by decide
  rcases family_descends (prefixWord ++ tailWord_745018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745034 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_745034 : Nat := 118140960795 + 745034 * 2 ^ 59
def prefixEnd_745034 : Nat := 4983230072969 + 3 ^ 40 * 745034 * 2
def baseEnd_745034 : Nat := 382560545941943284748657

theorem tailTrace_745034 : CollatzResearch.WordTrace tailWord_745034 prefixEnd_745034 382560545941943284748657 := by
  unfold tailWord_745034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793405595719133630520539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18115748255251023014721437 6793405595719133630520539)
  ·
    refine ⟨10190108393578700445780809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6793405595719133630520539 10190108393578700445780809)
    ·
      refine ⟨7642581295184025334335607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10190108393578700445780809 7642581295184025334335607)
      ·
        refine ⟨11463871942776038001503411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7642581295184025334335607 11463871942776038001503411)
        ·
          refine ⟨17195807914164057002255117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11463871942776038001503411 17195807914164057002255117)
          ·
            refine ⟨6448427967811521375845669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17195807914164057002255117 6448427967811521375845669)
            ·
              refine ⟨1209080243964660257971063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6448427967811521375845669 1209080243964660257971063)
              ·
                refine ⟨1813620365946990386956595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209080243964660257971063 1813620365946990386956595)
                ·
                  refine ⟨2720430548920485580434893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813620365946990386956595 2720430548920485580434893)
                  ·
                    refine ⟨1020161455845182092663085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2720430548920485580434893 1020161455845182092663085)
                    ·
                      refine ⟨382560545941943284748657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1020161455845182092663085 382560545941943284748657)
                      ·
                        rfl

theorem cell23_745034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_745034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745034 prefixEnd_745034 := by exact prefixLift 745034
  have htrace : WordTrace (prefixWord ++ tailWord_745034) baseStart_745034 baseEnd_745034 := by
    simpa [prefixWord, tailWord_745034, baseEnd_745034] using wordTrace_append hprefix tailTrace_745034
  have hstable : (prefixWord ++ tailWord_745034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745034).length < 2 ^ (prefixWord ++ tailWord_745034).sum := by decide
  have hdescent : baseEnd_745034 < baseStart_745034 := by decide
  rcases family_descends (prefixWord ++ tailWord_745034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745097 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 7]
def baseStart_745097 : Nat := 118140960795 + 745097 * 2 ^ 59
def prefixEnd_745097 : Nat := 4983230072969 + 3 ^ 40 * 745097 * 2
def baseEnd_745097 : Nat := 42510321691464059806763

theorem tailTrace_745097 : CollatzResearch.WordTrace tailWord_745097 prefixEnd_745097 42510321691464059806763 := by
  unfold tailWord_745097
  simp only [CollatzResearch.WordTrace]
  refine ⟨27175920181648296281625545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18117280121098864187750363 27175920181648296281625545)
  ·
    refine ⟨20381940136236222211219159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27175920181648296281625545 20381940136236222211219159)
    ·
      refine ⟨30572910204354333316828739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20381940136236222211219159 30572910204354333316828739)
      ·
        refine ⟨45859365306531499975243109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30572910204354333316828739 45859365306531499975243109)
        ·
          refine ⟨8598630994974656245358083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45859365306531499975243109 8598630994974656245358083)
          ·
            refine ⟨12897946492461984368037125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8598630994974656245358083 12897946492461984368037125)
            ·
              refine ⟨2418364967336622069006961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12897946492461984368037125 2418364967336622069006961)
              ·
                refine ⟨1813773725502466551755221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2418364967336622069006961 1813773725502466551755221)
                ·
                  refine ⟨42510321691464059806763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1813773725502466551755221 42510321691464059806763)
                  ·
                    rfl

theorem cell23_745097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 7].length) (baseStart_745097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745097 prefixEnd_745097 := by exact prefixLift 745097
  have htrace : WordTrace (prefixWord ++ tailWord_745097) baseStart_745097 baseEnd_745097 := by
    simpa [prefixWord, tailWord_745097, baseEnd_745097] using wordTrace_append hprefix tailTrace_745097
  have hstable : (prefixWord ++ tailWord_745097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745097).length < 2 ^ (prefixWord ++ tailWord_745097).sum := by decide
  have hdescent : baseEnd_745097 < baseStart_745097 := by decide
  rcases family_descends (prefixWord ++ tailWord_745097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745142 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_745142 : Nat := 118140960795 + 745142 * 2 ^ 59
def prefixEnd_745142 : Nat := 4983230072969 + 3 ^ 40 * 745142 * 2
def baseEnd_745142 : Nat := 382616001852628862198161

theorem tailTrace_745142 : CollatzResearch.WordTrace tailWord_745142 prefixEnd_745142 382616001852628862198161 := by
  unfold tailWord_745142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698597591655329310438355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18118374310990179311342453 1698597591655329310438355)
  ·
    refine ⟨2547896387482993965657533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1698597591655329310438355 2547896387482993965657533)
    ·
      refine ⟨955461145306122737121575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2547896387482993965657533 955461145306122737121575)
      ·
        refine ⟨1433191717959184105682363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955461145306122737121575 1433191717959184105682363)
        ·
          refine ⟨2149787576938776158523545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433191717959184105682363 2149787576938776158523545)
          ·
            refine ⟨1612340682704082118892659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2149787576938776158523545 1612340682704082118892659)
            ·
              refine ⟨2418511024056123178338989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612340682704082118892659 2418511024056123178338989)
              ·
                refine ⟨906941634021046191877121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2418511024056123178338989 906941634021046191877121)
                ·
                  refine ⟨680206225515784643907841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 906941634021046191877121 680206225515784643907841)
                  ·
                    refine ⟨510154669136838482930881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 680206225515784643907841 510154669136838482930881)
                    ·
                      refine ⟨382616001852628862198161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510154669136838482930881 382616001852628862198161)
                      ·
                        rfl

theorem cell23_745142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_745142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745142 prefixEnd_745142 := by exact prefixLift 745142
  have htrace : WordTrace (prefixWord ++ tailWord_745142) baseStart_745142 baseEnd_745142 := by
    simpa [prefixWord, tailWord_745142, baseEnd_745142] using wordTrace_append hprefix tailTrace_745142
  have hstable : (prefixWord ++ tailWord_745142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745142).length < 2 ^ (prefixWord ++ tailWord_745142).sum := by decide
  have hdescent : baseEnd_745142 < baseStart_745142 := by decide
  rcases family_descends (prefixWord ++ tailWord_745142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745147 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4]
def baseStart_745147 : Nat := 118140960795 + 745147 * 2 ^ 59
def prefixEnd_745147 : Nat := 4983230072969 + 3 ^ 40 * 745147 * 2
def baseEnd_745147 : Nat := 382618569255901342635637

theorem tailTrace_745147 : CollatzResearch.WordTrace tailWord_745147 prefixEnd_745147 382618569255901342635637 := by
  unfold tailWord_745147
  simp only [CollatzResearch.WordTrace]
  refine ⟨27177743831467154820945695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18118495887644769880630463 27177743831467154820945695)
  ·
    refine ⟨40766615747200732231418543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27177743831467154820945695 40766615747200732231418543)
    ·
      refine ⟨61149923620801098347127815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40766615747200732231418543 61149923620801098347127815)
      ·
        refine ⟨91724885431201647520691723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61149923620801098347127815 91724885431201647520691723)
        ·
          refine ⟨137587328146802471281037585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91724885431201647520691723 137587328146802471281037585)
          ·
            refine ⟨103190496110101853460778189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137587328146802471281037585 103190496110101853460778189)
            ·
              refine ⟨38696436041288195047791821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103190496110101853460778189 38696436041288195047791821)
              ·
                refine ⟨14511163515483073142921933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38696436041288195047791821 14511163515483073142921933)
                ·
                  refine ⟨5441686318306152428595725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14511163515483073142921933 5441686318306152428595725)
                  ·
                    refine ⟨2040632369364807160723397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5441686318306152428595725 2040632369364807160723397)
                    ·
                      refine ⟨382618569255901342635637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2040632369364807160723397 382618569255901342635637)
                      ·
                        rfl

theorem cell23_745147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4].length) (baseStart_745147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745147 prefixEnd_745147 := by exact prefixLift 745147
  have htrace : WordTrace (prefixWord ++ tailWord_745147) baseStart_745147 baseEnd_745147 := by
    simpa [prefixWord, tailWord_745147, baseEnd_745147] using wordTrace_append hprefix tailTrace_745147
  have hstable : (prefixWord ++ tailWord_745147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745147).length < 2 ^ (prefixWord ++ tailWord_745147).sum := by decide
  have hdescent : baseEnd_745147 < baseStart_745147 := by decide
  rcases family_descends (prefixWord ++ tailWord_745147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745248 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 3, 1, 3]
def baseStart_745248 : Nat := 118140960795 + 745248 * 2 ^ 59
def prefixEnd_745248 : Nat := 4983230072969 + 3 ^ 40 * 745248 * 2
def baseEnd_745248 : Nat := 382670430802005447472673

theorem tailTrace_745248 : CollatzResearch.WordTrace tailWord_745248 prefixEnd_745248 382670430802005447472673 := by
  unfold tailWord_745248
  simp only [CollatzResearch.WordTrace]
  refine ⟨13590713802050624535186199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18120951736067499380248265 13590713802050624535186199)
  ·
    refine ⟨20386070703075936802779299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13590713802050624535186199 20386070703075936802779299)
    ·
      refine ⟨30579106054613905204168949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20386070703075936802779299 30579106054613905204168949)
      ·
        refine ⟨2866791192620053612890839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30579106054613905204168949 2866791192620053612890839)
        ·
          refine ⟨4300186788930080419336259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866791192620053612890839 4300186788930080419336259)
          ·
            refine ⟨6450280183395120629004389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300186788930080419336259 6450280183395120629004389)
            ·
              refine ⟨1209427534386585117938323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6450280183395120629004389 1209427534386585117938323)
              ·
                refine ⟨1814141301579877676907485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209427534386585117938323 1814141301579877676907485)
                ·
                  refine ⟨680302988092454128840307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1814141301579877676907485 680302988092454128840307)
                  ·
                    refine ⟨1020454482138681193260461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 680302988092454128840307 1020454482138681193260461)
                    ·
                      refine ⟨382670430802005447472673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1020454482138681193260461 382670430802005447472673)
                      ·
                        rfl

theorem cell23_745248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_745248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745248 prefixEnd_745248 := by exact prefixLift 745248
  have htrace : WordTrace (prefixWord ++ tailWord_745248) baseStart_745248 baseEnd_745248 := by
    simpa [prefixWord, tailWord_745248, baseEnd_745248] using wordTrace_append hprefix tailTrace_745248
  have hstable : (prefixWord ++ tailWord_745248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745248).length < 2 ^ (prefixWord ++ tailWord_745248).sum := by decide
  have hdescent : baseEnd_745248 < baseStart_745248 := by decide
  rcases family_descends (prefixWord ++ tailWord_745248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745268 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_745268 : Nat := 118140960795 + 745268 * 2 ^ 59
def prefixEnd_745268 : Nat := 4983230072969 + 3 ^ 40 * 745268 * 2
def baseEnd_745268 : Nat := 127560233471698456407527

theorem tailTrace_745268 : CollatzResearch.WordTrace tailWord_745268 prefixEnd_745268 127560233471698456407527 := by
  unfold tailWord_745268
  simp only [CollatzResearch.WordTrace]
  refine ⟨13591078532014396243050229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18121438042685861657400305 13591078532014396243050229)
  ·
    refine ⟨1274163612376349647785959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13591078532014396243050229 1274163612376349647785959)
    ·
      refine ⟨1911245418564524471678939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1274163612376349647785959 1911245418564524471678939)
      ·
        refine ⟨2866868127846786707518409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1911245418564524471678939 2866868127846786707518409)
        ·
          refine ⟨2150151095885090030638807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2866868127846786707518409 2150151095885090030638807)
          ·
            refine ⟨3225226643827635045958211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150151095885090030638807 3225226643827635045958211)
            ·
              refine ⟨4837839965741452568937317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3225226643827635045958211 4837839965741452568937317)
              ·
                refine ⟨907094993576522356675747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4837839965741452568937317 907094993576522356675747)
                ·
                  refine ⟨1360642490364783535013621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907094993576522356675747 1360642490364783535013621)
                  ·
                    refine ⟨127560233471698456407527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1360642490364783535013621 127560233471698456407527)
                    ·
                      rfl

theorem cell23_745268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_745268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745268 prefixEnd_745268 := by exact prefixLift 745268
  have htrace : WordTrace (prefixWord ++ tailWord_745268) baseStart_745268 baseEnd_745268 := by
    simpa [prefixWord, tailWord_745268, baseEnd_745268] using wordTrace_append hprefix tailTrace_745268
  have hstable : (prefixWord ++ tailWord_745268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745268).length < 2 ^ (prefixWord ++ tailWord_745268).sum := by decide
  have hdescent : baseEnd_745268 < baseStart_745268 := by decide
  rcases family_descends (prefixWord ++ tailWord_745268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745322 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_745322 : Nat := 118140960795 + 745322 * 2 ^ 59
def prefixEnd_745322 : Nat := 4983230072969 + 3 ^ 40 * 745322 * 2
def baseEnd_745322 : Nat := 382708428370438157947333

theorem tailTrace_745322 : CollatzResearch.WordTrace tailWord_745322 prefixEnd_745322 382708428370438157947333 := by
  unfold tailWord_745322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6796031651458289927141555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18122751070555439805710813 6796031651458289927141555)
  ·
    refine ⟨10194047477187434890712333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6796031651458289927141555 10194047477187434890712333)
    ·
      refine ⟨3822767803945288084017125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10194047477187434890712333 3822767803945288084017125)
      ·
        refine ⟨716768963239741515753211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3822767803945288084017125 716768963239741515753211)
        ·
          refine ⟨1075153444859612273629817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716768963239741515753211 1075153444859612273629817)
          ·
            refine ⟨806365083644709205222363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1075153444859612273629817 806365083644709205222363)
            ·
              refine ⟨1209547625467063807833545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806365083644709205222363 1209547625467063807833545)
              ·
                refine ⟨907160719100297855875159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209547625467063807833545 907160719100297855875159)
                ·
                  refine ⟨1360741078650446783812739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907160719100297855875159 1360741078650446783812739)
                  ·
                    refine ⟨2041111617975670175719109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1360741078650446783812739 2041111617975670175719109)
                    ·
                      refine ⟨382708428370438157947333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2041111617975670175719109 382708428370438157947333)
                      ·
                        rfl

theorem cell23_745322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_745322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745322 prefixEnd_745322 := by exact prefixLift 745322
  have htrace : WordTrace (prefixWord ++ tailWord_745322) baseStart_745322 baseEnd_745322 := by
    simpa [prefixWord, tailWord_745322, baseEnd_745322] using wordTrace_append hprefix tailTrace_745322
  have hstable : (prefixWord ++ tailWord_745322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745322).length < 2 ^ (prefixWord ++ tailWord_745322).sum := by decide
  have hdescent : baseEnd_745322 < baseStart_745322 := by decide
  rcases family_descends (prefixWord ++ tailWord_745322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745418 : List Nat := [3, 1, 2, 1, 2, 1, 4, 4, 5]
def baseStart_745418 : Nat := 118140960795 + 745418 * 2 ^ 59
def prefixEnd_745418 : Nat := 4983230072969 + 3 ^ 40 * 745418 * 2
def baseEnd_745418 : Nat := 42528635834807753594099

theorem tailTrace_745418 : CollatzResearch.WordTrace tailWord_745418 prefixEnd_745418 42528635834807753594099 := by
  unfold tailWord_745418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6796907003371342026015227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18125085342323578736040605 6796907003371342026015227)
  ·
    refine ⟨10195360505057013039022841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6796907003371342026015227 10195360505057013039022841)
    ·
      refine ⟨7646520378792759779267131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10195360505057013039022841 7646520378792759779267131)
      ·
        refine ⟨11469780568189139668900697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7646520378792759779267131 11469780568189139668900697)
        ·
          refine ⟨8602335426141854751675523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11469780568189139668900697 8602335426141854751675523)
          ·
            refine ⟨12903503139212782127513285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8602335426141854751675523 12903503139212782127513285)
            ·
              refine ⟨2419406838602396648908741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12903503139212782127513285 2419406838602396648908741)
              ·
                refine ⟨453638782237949371670389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2419406838602396648908741 453638782237949371670389)
                ·
                  refine ⟨42528635834807753594099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 453638782237949371670389 42528635834807753594099)
                  ·
                    rfl

theorem cell23_745418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_745418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745418 prefixEnd_745418 := by exact prefixLift 745418
  have htrace : WordTrace (prefixWord ++ tailWord_745418) baseStart_745418 baseEnd_745418 := by
    simpa [prefixWord, tailWord_745418, baseEnd_745418] using wordTrace_append hprefix tailTrace_745418
  have hstable : (prefixWord ++ tailWord_745418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745418).length < 2 ^ (prefixWord ++ tailWord_745418).sum := by decide
  have hdescent : baseEnd_745418 < baseStart_745418 := by decide
  rcases family_descends (prefixWord ++ tailWord_745418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745428 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_745428 : Nat := 118140960795 + 745428 * 2 ^ 59
def prefixEnd_745428 : Nat := 4983230072969 + 3 ^ 40 * 745428 * 2
def baseEnd_745428 : Nat := 382762857319814743221845

theorem tailTrace_745428 : CollatzResearch.WordTrace tailWord_745428 prefixEnd_745428 382762857319814743221845 := by
  unfold tailWord_745428
  simp only [CollatzResearch.WordTrace]
  refine ⟨13593996371724569905962469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18125328495632759874616625 13593996371724569905962469)
  ·
    refine ⟨2548874319698356857367963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13593996371724569905962469 2548874319698356857367963)
    ·
      refine ⟨3823311479547535286051945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2548874319698356857367963 3823311479547535286051945)
      ·
        refine ⟨2867483609660651464538959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3823311479547535286051945 2867483609660651464538959)
        ·
          refine ⟨4301225414490977196808439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2867483609660651464538959 4301225414490977196808439)
          ·
            refine ⟨6451838121736465795212659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301225414490977196808439 6451838121736465795212659)
            ·
              refine ⟨9677757182604698692818989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451838121736465795212659 9677757182604698692818989)
              ·
                refine ⟨3629158943476762009807121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9677757182604698692818989 3629158943476762009807121)
                ·
                  refine ⟨2721869207607571507355341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3629158943476762009807121 2721869207607571507355341)
                  ·
                    refine ⟨1020700952852839315258253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2721869207607571507355341 1020700952852839315258253)
                    ·
                      refine ⟨382762857319814743221845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1020700952852839315258253 382762857319814743221845)
                      ·
                        rfl

theorem cell23_745428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_745428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745428 prefixEnd_745428 := by exact prefixLift 745428
  have htrace : WordTrace (prefixWord ++ tailWord_745428) baseStart_745428 baseEnd_745428 := by
    simpa [prefixWord, tailWord_745428, baseEnd_745428] using wordTrace_append hprefix tailTrace_745428
  have hstable : (prefixWord ++ tailWord_745428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745428).length < 2 ^ (prefixWord ++ tailWord_745428).sum := by decide
  have hdescent : baseEnd_745428 < baseStart_745428 := by decide
  rcases family_descends (prefixWord ++ tailWord_745428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745429 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 2, 2, 2]
def baseStart_745429 : Nat := 118140960795 + 745429 * 2 ^ 59
def prefixEnd_745429 : Nat := 4983230072969 + 3 ^ 40 * 745429 * 2
def baseEnd_745429 : Nat := 382763370800469239309341

theorem tailTrace_745429 : CollatzResearch.WordTrace tailWord_745429 prefixEnd_745429 382763370800469239309341 := by
  unfold tailWord_745429
  simp only [CollatzResearch.WordTrace]
  refine ⟨27188029216445516982711341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18125352810963677988474227 27188029216445516982711341)
  ·
    refine ⟨10195510956167068868516753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27188029216445516982711341 10195510956167068868516753)
    ·
      refine ⟨7646633217125301651387565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10195510956167068868516753 7646633217125301651387565)
      ·
        refine ⟨2867487456421988119270337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7646633217125301651387565 2867487456421988119270337)
        ·
          refine ⟨2150615592316491089452753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2867487456421988119270337 2150615592316491089452753)
          ·
            refine ⟨1612961694237368317089565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2150615592316491089452753 1612961694237368317089565)
            ·
              refine ⟨604860635339013118908587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1612961694237368317089565 604860635339013118908587)
              ·
                refine ⟨907290953008519678362881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604860635339013118908587 907290953008519678362881)
                ·
                  refine ⟨680468214756389758772161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 907290953008519678362881 680468214756389758772161)
                  ·
                    refine ⟨510351161067292319079121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 680468214756389758772161 510351161067292319079121)
                    ·
                      refine ⟨382763370800469239309341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510351161067292319079121 382763370800469239309341)
                      ·
                        rfl

theorem cell23_745429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_745429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745429 prefixEnd_745429 := by exact prefixLift 745429
  have htrace : WordTrace (prefixWord ++ tailWord_745429) baseStart_745429 baseEnd_745429 := by
    simpa [prefixWord, tailWord_745429, baseEnd_745429] using wordTrace_append hprefix tailTrace_745429
  have hstable : (prefixWord ++ tailWord_745429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745429).length < 2 ^ (prefixWord ++ tailWord_745429).sum := by decide
  have hdescent : baseEnd_745429 < baseStart_745429 := by decide
  rcases family_descends (prefixWord ++ tailWord_745429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745451 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 4]
def baseStart_745451 : Nat := 118140960795 + 745451 * 2 ^ 59
def prefixEnd_745451 : Nat := 4983230072969 + 3 ^ 40 * 745451 * 2
def baseEnd_745451 : Nat := 382774667374868153234239

theorem tailTrace_745451 : CollatzResearch.WordTrace tailWord_745451 prefixEnd_745451 382774667374868153234239 := by
  unfold tailWord_745451
  simp only [CollatzResearch.WordTrace]
  refine ⟨27188831622365814740012207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18125887748243876493341471 27188831622365814740012207)
  ·
    refine ⟨40783247433548722110018311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27188831622365814740012207 40783247433548722110018311)
    ·
      refine ⟨61174871150323083165027467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40783247433548722110018311 61174871150323083165027467)
      ·
        refine ⟨91762306725484624747541201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61174871150323083165027467 91762306725484624747541201)
        ·
          refine ⟨68821730044113468560655901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91762306725484624747541201 68821730044113468560655901)
          ·
            refine ⟨25808148766542550710245963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68821730044113468560655901 25808148766542550710245963)
            ·
              refine ⟨38712223149813826065368945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25808148766542550710245963 38712223149813826065368945)
              ·
                refine ⟨29034167362360369549026709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38712223149813826065368945 29034167362360369549026709)
                ·
                  refine ⟨1360976595110642322610627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29034167362360369549026709 1360976595110642322610627)
                  ·
                    refine ⟨2041464892665963483915941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1360976595110642322610627 2041464892665963483915941)
                    ·
                      refine ⟨382774667374868153234239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2041464892665963483915941 382774667374868153234239)
                      ·
                        rfl

theorem cell23_745451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 4].length) (baseStart_745451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745451 prefixEnd_745451 := by exact prefixLift 745451
  have htrace : WordTrace (prefixWord ++ tailWord_745451) baseStart_745451 baseEnd_745451 := by
    simpa [prefixWord, tailWord_745451, baseEnd_745451] using wordTrace_append hprefix tailTrace_745451
  have hstable : (prefixWord ++ tailWord_745451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745451).length < 2 ^ (prefixWord ++ tailWord_745451).sum := by decide
  have hdescent : baseEnd_745451 < baseStart_745451 := by decide
  rcases family_descends (prefixWord ++ tailWord_745451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745468 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_745468 : Nat := 118140960795 + 745468 * 2 ^ 59
def prefixEnd_745468 : Nat := 4983230072969 + 3 ^ 40 * 745468 * 2
def baseEnd_745468 : Nat := 382783396545994586721661

theorem tailTrace_745468 : CollatzResearch.WordTrace tailWord_745468 prefixEnd_745468 382783396545994586721661 := by
  unfold tailWord_745468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13594725831652113321690529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18126301108869484428920705 13594725831652113321690529)
  ·
    refine ⟨10196044373739084991267897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13594725831652113321690529 10196044373739084991267897)
    ·
      refine ⟨7647033280304313743450923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10196044373739084991267897 7647033280304313743450923)
      ·
        refine ⟨11470549920456470615176385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7647033280304313743450923 11470549920456470615176385)
        ·
          refine ⟨8602912440342352961382289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11470549920456470615176385 8602912440342352961382289)
          ·
            refine ⟨6452184330256764721036717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8602912440342352961382289 6452184330256764721036717)
            ·
              refine ⟨2419569123846286770388769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6452184330256764721036717 2419569123846286770388769)
              ·
                refine ⟨1814676842884715077791577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2419569123846286770388769 1814676842884715077791577)
                ·
                  refine ⟨1361007632163536308343683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1814676842884715077791577 1361007632163536308343683)
                  ·
                    refine ⟨2041511448245304462515525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1361007632163536308343683 2041511448245304462515525)
                    ·
                      refine ⟨382783396545994586721661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2041511448245304462515525 382783396545994586721661)
                      ·
                        rfl

theorem cell23_745468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_745468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745468 prefixEnd_745468 := by exact prefixLift 745468
  have htrace : WordTrace (prefixWord ++ tailWord_745468) baseStart_745468 baseEnd_745468 := by
    simpa [prefixWord, tailWord_745468, baseEnd_745468] using wordTrace_append hprefix tailTrace_745468
  have hstable : (prefixWord ++ tailWord_745468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745468).length < 2 ^ (prefixWord ++ tailWord_745468).sum := by decide
  have hdescent : baseEnd_745468 < baseStart_745468 := by decide
  rcases family_descends (prefixWord ++ tailWord_745468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745551 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 5, 6]
def baseStart_745551 : Nat := 118140960795 + 745551 * 2 ^ 59
def prefixEnd_745551 : Nat := 4983230072969 + 3 ^ 40 * 745551 * 2
def baseEnd_745551 : Nat := 127608671813439253994593

theorem tailTrace_745551 : CollatzResearch.WordTrace tailWord_745551 prefixEnd_745551 127608671813439253994593 := by
  unfold tailWord_745551
  simp only [CollatzResearch.WordTrace]
  refine ⟨27192478922003531818652507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18128319281335687879101671 27192478922003531818652507)
  ·
    refine ⟨40788718383005297727978761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27192478922003531818652507 40788718383005297727978761)
    ·
      refine ⟨30591538787253973295984071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40788718383005297727978761 30591538787253973295984071)
      ·
        refine ⟨45887308180880959943976107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30591538787253973295984071 45887308180880959943976107)
        ·
          refine ⟨68830962271321439915964161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45887308180880959943976107 68830962271321439915964161)
          ·
            refine ⟨51623221703491079936973121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68830962271321439915964161 51623221703491079936973121)
            ·
              refine ⟨38717416277618309952729841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51623221703491079936973121 38717416277618309952729841)
              ·
                refine ⟨29038062208213732464547381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38717416277618309952729841 29038062208213732464547381)
                ·
                  refine ⟨2722318332020037418551317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29038062208213732464547381 2722318332020037418551317)
                  ·
                    refine ⟨127608671813439253994593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2722318332020037418551317 127608671813439253994593)
                    ·
                      rfl

theorem cell23_745551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_745551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745551 prefixEnd_745551 := by exact prefixLift 745551
  have htrace : WordTrace (prefixWord ++ tailWord_745551) baseStart_745551 baseEnd_745551 := by
    simpa [prefixWord, tailWord_745551, baseEnd_745551] using wordTrace_append hprefix tailTrace_745551
  have hstable : (prefixWord ++ tailWord_745551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745551).length < 2 ^ (prefixWord ++ tailWord_745551).sum := by decide
  have hdescent : baseEnd_745551 < baseStart_745551 := by decide
  rcases family_descends (prefixWord ++ tailWord_745551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745568 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 1, 6]
def baseStart_745568 : Nat := 118140960795 + 745568 * 2 ^ 59
def prefixEnd_745568 : Nat := 4983230072969 + 3 ^ 40 * 745568 * 2
def baseEnd_745568 : Nat := 127611581537148065157067

theorem tailTrace_745568 : CollatzResearch.WordTrace tailWord_745568 prefixEnd_745568 127611581537148065157067 := by
  unfold tailWord_745568
  simp only [CollatzResearch.WordTrace]
  refine ⟨13596549481470971861010679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18128732641961295814680905 13596549481470971861010679)
  ·
    refine ⟨20394824222206457791516019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13596549481470971861010679 20394824222206457791516019)
    ·
      refine ⟨30592236333309686687274029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20394824222206457791516019 30592236333309686687274029)
      ·
        refine ⟨11472088624991132507727761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30592236333309686687274029 11472088624991132507727761)
        ·
          refine ⟨8604066468743349380795821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11472088624991132507727761 8604066468743349380795821)
          ·
            refine ⟨3226524925778756017798433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8604066468743349380795821 3226524925778756017798433)
            ·
              refine ⟨2419893694334067013348825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226524925778756017798433 2419893694334067013348825)
              ·
                refine ⟨1814920270750550260011619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2419893694334067013348825 1814920270750550260011619)
                ·
                  refine ⟨2722380406125825390017429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1814920270750550260011619 2722380406125825390017429)
                  ·
                    refine ⟨127611581537148065157067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2722380406125825390017429 127611581537148065157067)
                    ·
                      rfl

theorem cell23_745568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_745568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745568 prefixEnd_745568 := by exact prefixLift 745568
  have htrace : WordTrace (prefixWord ++ tailWord_745568) baseStart_745568 baseEnd_745568 := by
    simpa [prefixWord, tailWord_745568, baseEnd_745568] using wordTrace_append hprefix tailTrace_745568
  have hstable : (prefixWord ++ tailWord_745568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745568).length < 2 ^ (prefixWord ++ tailWord_745568).sum := by decide
  have hdescent : baseEnd_745568 < baseStart_745568 := by decide
  rcases family_descends (prefixWord ++ tailWord_745568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745575 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_745575 : Nat := 118140960795 + 745575 * 2 ^ 59
def prefixEnd_745575 : Nat := 4983230072969 + 3 ^ 40 * 745575 * 2
def baseEnd_745575 : Nat := 382838338976025668083669

theorem tailTrace_745575 : CollatzResearch.WordTrace tailWord_745575 prefixEnd_745575 382838338976025668083669 := by
  unfold tailWord_745575
  simp only [CollatzResearch.WordTrace]
  refine ⟨27193354273916583917526179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18128902849277722611684119 27193354273916583917526179)
  ·
    refine ⟨40790031410874875876289269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27193354273916583917526179 40790031410874875876289269)
    ·
      refine ⟨3824065444769519613402119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40790031410874875876289269 3824065444769519613402119)
      ·
        refine ⟨5736098167154279420103179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3824065444769519613402119 5736098167154279420103179)
        ·
          refine ⟨8604147250731419130154769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5736098167154279420103179 8604147250731419130154769)
          ·
            refine ⟨6453110438048564347616077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8604147250731419130154769 6453110438048564347616077)
            ·
              refine ⟨2419916414268211630356029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6453110438048564347616077 2419916414268211630356029)
              ·
                refine ⟨907468655350579361383511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2419916414268211630356029 907468655350579361383511)
                ·
                  refine ⟨1361202983025869042075267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907468655350579361383511 1361202983025869042075267)
                  ·
                    refine ⟨2041804474538803563112901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1361202983025869042075267 2041804474538803563112901)
                    ·
                      refine ⟨382838338976025668083669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2041804474538803563112901 382838338976025668083669)
                      ·
                        rfl

theorem cell23_745575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_745575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745575 prefixEnd_745575 := by exact prefixLift 745575
  have htrace : WordTrace (prefixWord ++ tailWord_745575) baseStart_745575 baseEnd_745575 := by
    simpa [prefixWord, tailWord_745575, baseEnd_745575] using wordTrace_append hprefix tailTrace_745575
  have hstable : (prefixWord ++ tailWord_745575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745575).length < 2 ^ (prefixWord ++ tailWord_745575).sum := by decide
  have hdescent : baseEnd_745575 < baseStart_745575 := by decide
  rcases family_descends (prefixWord ++ tailWord_745575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745605 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 4]
def baseStart_745605 : Nat := 118140960795 + 745605 * 2 ^ 59
def prefixEnd_745605 : Nat := 4983230072969 + 3 ^ 40 * 745605 * 2
def baseEnd_745605 : Nat := 382853743395660550708531

theorem tailTrace_745605 : CollatzResearch.WordTrace tailWord_745605 prefixEnd_745605 382853743395660550708531 := by
  unfold tailWord_745605
  simp only [CollatzResearch.WordTrace]
  refine ⟨27194448463807899041118269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18129632309205266027412179 27194448463807899041118269)
  ·
    refine ⟨10197918173927962140419351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27194448463807899041118269 10197918173927962140419351)
    ·
      refine ⟨15296877260891943210629027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10197918173927962140419351 15296877260891943210629027)
      ·
        refine ⟨22945315891337914815943541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15296877260891943210629027 22945315891337914815943541)
        ·
          refine ⟨2151123364812929513994707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22945315891337914815943541 2151123364812929513994707)
          ·
            refine ⟨3226685047219394270992061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151123364812929513994707 3226685047219394270992061)
            ·
              refine ⟨1210006892707272851622023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3226685047219394270992061 1210006892707272851622023)
              ·
                refine ⟨1815010339060909277433035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210006892707272851622023 1815010339060909277433035)
                ·
                  refine ⟨2722515508591363916149553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815010339060909277433035 2722515508591363916149553)
                  ·
                    refine ⟨2041886631443522937112165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2722515508591363916149553 2041886631443522937112165)
                    ·
                      refine ⟨382853743395660550708531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2041886631443522937112165 382853743395660550708531)
                      ·
                        rfl

theorem cell23_745605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 4].length) (baseStart_745605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745605 prefixEnd_745605 := by exact prefixLift 745605
  have htrace : WordTrace (prefixWord ++ tailWord_745605) baseStart_745605 baseEnd_745605 := by
    simpa [prefixWord, tailWord_745605, baseEnd_745605] using wordTrace_append hprefix tailTrace_745605
  have hstable : (prefixWord ++ tailWord_745605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745605).length < 2 ^ (prefixWord ++ tailWord_745605).sum := by decide
  have hdescent : baseEnd_745605 < baseStart_745605 := by decide
  rcases family_descends (prefixWord ++ tailWord_745605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745620 : List Nat := [2, 4, 2, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_745620 : Nat := 118140960795 + 745620 * 2 ^ 59
def prefixEnd_745620 : Nat := 4983230072969 + 3 ^ 40 * 745620 * 2
def baseEnd_745620 : Nat := 382861445605477992020963

theorem tailTrace_745620 : CollatzResearch.WordTrace tailWord_745620 prefixEnd_745620 382861445605477992020963 := by
  unfold tailWord_745620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13597497779376778301457157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18129997039169037735276209 13597497779376778301457157)
  ·
    refine ⟨2549530833633145931523217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13597497779376778301457157 2549530833633145931523217)
    ·
      refine ⟨1912148125224859448642413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2549530833633145931523217 1912148125224859448642413)
      ·
        refine ⟨717055546959322293240905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1912148125224859448642413 717055546959322293240905)
        ·
          refine ⟨537791660219491719930679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717055546959322293240905 537791660219491719930679)
          ·
            refine ⟨806687490329237579896019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537791660219491719930679 806687490329237579896019)
            ·
              refine ⟨1210031235493856369844029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806687490329237579896019 1210031235493856369844029)
              ·
                refine ⟨453761713310196138691511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1210031235493856369844029 453761713310196138691511)
                ·
                  refine ⟨680642569965294208037267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453761713310196138691511 680642569965294208037267)
                  ·
                    refine ⟨1020963854947941312055901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 680642569965294208037267 1020963854947941312055901)
                    ·
                      refine ⟨382861445605477992020963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1020963854947941312055901 382861445605477992020963)
                      ·
                        rfl

theorem cell23_745620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_745620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745620 prefixEnd_745620 := by exact prefixLift 745620
  have htrace : WordTrace (prefixWord ++ tailWord_745620) baseStart_745620 baseEnd_745620 := by
    simpa [prefixWord, tailWord_745620, baseEnd_745620] using wordTrace_append hprefix tailTrace_745620
  have hstable : (prefixWord ++ tailWord_745620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745620).length < 2 ^ (prefixWord ++ tailWord_745620).sum := by decide
  have hdescent : baseEnd_745620 < baseStart_745620 := by decide
  rcases family_descends (prefixWord ++ tailWord_745620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745635 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 7, 3, 2]
def baseStart_745635 : Nat := 118140960795 + 745635 * 2 ^ 59
def prefixEnd_745635 : Nat := 4983230072969 + 3 ^ 40 * 745635 * 2
def baseEnd_745635 : Nat := 382869147815295433333393

theorem tailTrace_745635 : CollatzResearch.WordTrace tailWord_745635 prefixEnd_745635 382869147815295433333393 := by
  unfold tailWord_745635
  simp only [CollatzResearch.WordTrace]
  refine ⟨27195542653699214164710359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18130361769132809443140239 27195542653699214164710359)
  ·
    refine ⟨40793313980548821247065539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27195542653699214164710359 40793313980548821247065539)
    ·
      refine ⟨61189970970823231870598309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40793313980548821247065539 61189970970823231870598309)
      ·
        refine ⟨11473119557029355975737183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61189970970823231870598309 11473119557029355975737183)
        ·
          refine ⟨17209679335544033963605775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11473119557029355975737183 17209679335544033963605775)
          ·
            refine ⟨25814519003316050945408663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17209679335544033963605775 25814519003316050945408663)
            ·
              refine ⟨38721778504974076418112995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25814519003316050945408663 38721778504974076418112995)
              ·
                refine ⟨58082667757461114627169493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38721778504974076418112995 58082667757461114627169493)
                ·
                  refine ⟨1361312525565494874074285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 58082667757461114627169493 1361312525565494874074285)
                  ·
                    refine ⟨510492197087060577777857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1361312525565494874074285 510492197087060577777857)
                    ·
                      refine ⟨382869147815295433333393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510492197087060577777857 382869147815295433333393)
                      ·
                        rfl

theorem cell23_745635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_745635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745635 prefixEnd_745635 := by exact prefixLift 745635
  have htrace : WordTrace (prefixWord ++ tailWord_745635) baseStart_745635 baseEnd_745635 := by
    simpa [prefixWord, tailWord_745635, baseEnd_745635] using wordTrace_append hprefix tailTrace_745635
  have hstable : (prefixWord ++ tailWord_745635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745635).length < 2 ^ (prefixWord ++ tailWord_745635).sum := by decide
  have hdescent : baseEnd_745635 < baseStart_745635 := by decide
  rcases family_descends (prefixWord ++ tailWord_745635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745653 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_745653 : Nat := 118140960795 + 745653 * 2 ^ 59
def prefixEnd_745653 : Nat := 4983230072969 + 3 ^ 40 * 745653 * 2
def baseEnd_745653 : Nat := 127626130155692120969437

theorem tailTrace_745653 : CollatzResearch.WordTrace tailWord_745653 prefixEnd_745653 127626130155692120969437 := by
  unfold tailWord_745653
  simp only [CollatzResearch.WordTrace]
  refine ⟨27196199167634003238865613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18130799445089335492577075 27196199167634003238865613)
  ·
    refine ⟨10198574687862751214574605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27196199167634003238865613 10198574687862751214574605)
    ·
      refine ⟨3824465507948531705465477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10198574687862751214574605 3824465507948531705465477)
      ·
        refine ⟨717087282740349694774777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3824465507948531705465477 717087282740349694774777)
        ·
          refine ⟨537815462055262271081083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717087282740349694774777 537815462055262271081083)
          ·
            refine ⟨806723193082893406621625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537815462055262271081083 806723193082893406621625)
            ·
              refine ⟨605042394812170054966219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806723193082893406621625 605042394812170054966219)
              ·
                refine ⟨907563592218255082449329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605042394812170054966219 907563592218255082449329)
                ·
                  refine ⟨680672694163691311836997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 907563592218255082449329 680672694163691311836997)
                  ·
                    refine ⟨127626130155692120969437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 680672694163691311836997 127626130155692120969437)
                    ·
                      rfl

theorem cell23_745653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_745653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745653 prefixEnd_745653 := by exact prefixLift 745653
  have htrace : WordTrace (prefixWord ++ tailWord_745653) baseStart_745653 baseEnd_745653 := by
    simpa [prefixWord, tailWord_745653, baseEnd_745653] using wordTrace_append hprefix tailTrace_745653
  have hstable : (prefixWord ++ tailWord_745653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745653).length < 2 ^ (prefixWord ++ tailWord_745653).sum := by decide
  have hdescent : baseEnd_745653 < baseStart_745653 := by decide
  rcases family_descends (prefixWord ++ tailWord_745653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745658 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_745658 : Nat := 118140960795 + 745658 * 2 ^ 59
def prefixEnd_745658 : Nat := 4983230072969 + 3 ^ 40 * 745658 * 2
def baseEnd_745658 : Nat := 127626985956782947781929

theorem tailTrace_745658 : CollatzResearch.WordTrace tailWord_745658 prefixEnd_745658 127626985956782947781929 := by
  unfold tailWord_745658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6799095383153972273199407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18130921021743926061865085 6799095383153972273199407)
  ·
    refine ⟨10198643074730958409799111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6799095383153972273199407 10198643074730958409799111)
    ·
      refine ⟨15297964612096437614698667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10198643074730958409799111 15297964612096437614698667)
      ·
        refine ⟨22946946918144656422048001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15297964612096437614698667 22946946918144656422048001)
        ·
          refine ⟨17210210188608492316536001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22946946918144656422048001 17210210188608492316536001)
          ·
            refine ⟨12907657641456369237402001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17210210188608492316536001 12907657641456369237402001)
            ·
              refine ⟨9680743231092276928051501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12907657641456369237402001 9680743231092276928051501)
              ·
                refine ⟨3630278711659603848019313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9680743231092276928051501 3630278711659603848019313)
                ·
                  refine ⟨2722709033744702886014485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3630278711659603848019313 2722709033744702886014485)
                  ·
                    refine ⟨127626985956782947781929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2722709033744702886014485 127626985956782947781929)
                    ·
                      rfl

theorem cell23_745658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_745658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745658 prefixEnd_745658 := by exact prefixLift 745658
  have htrace : WordTrace (prefixWord ++ tailWord_745658) baseStart_745658 baseEnd_745658 := by
    simpa [prefixWord, tailWord_745658, baseEnd_745658] using wordTrace_append hprefix tailTrace_745658
  have hstable : (prefixWord ++ tailWord_745658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745658).length < 2 ^ (prefixWord ++ tailWord_745658).sum := by decide
  have hdescent : baseEnd_745658 < baseStart_745658 := by decide
  rcases family_descends (prefixWord ++ tailWord_745658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745682 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_745682 : Nat := 118140960795 + 745682 * 2 ^ 59
def prefixEnd_745682 : Nat := 4983230072969 + 3 ^ 40 * 745682 * 2
def baseEnd_745682 : Nat := 382893281406056749445677

theorem tailTrace_745682 : CollatzResearch.WordTrace tailWord_745682 prefixEnd_745682 382893281406056749445677 := by
  unfold tailWord_745682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6799314221132235297917825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18131504589685960794447533 6799314221132235297917825)
  ·
    refine ⟨5099485665849176473438369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6799314221132235297917825 5099485665849176473438369)
    ·
      refine ⟨3824614249386882355078777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5099485665849176473438369 3824614249386882355078777)
      ·
        refine ⟨2868460687040161766309083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3824614249386882355078777 2868460687040161766309083)
        ·
          refine ⟨4302691030560242649463625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2868460687040161766309083 4302691030560242649463625)
          ·
            refine ⟨3227018272920181987097719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4302691030560242649463625 3227018272920181987097719)
            ·
              refine ⟨4840527409380272980646579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227018272920181987097719 4840527409380272980646579)
              ·
                refine ⟨7260791114070409470969869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4840527409380272980646579 7260791114070409470969869)
                ·
                  refine ⟨2722796667776403551613701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7260791114070409470969869 2722796667776403551613701)
                  ·
                    refine ⟨510524375208075665927569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2722796667776403551613701 510524375208075665927569)
                    ·
                      refine ⟨382893281406056749445677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510524375208075665927569 382893281406056749445677)
                      ·
                        rfl

theorem cell23_745682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_745682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745682 prefixEnd_745682 := by exact prefixLift 745682
  have htrace : WordTrace (prefixWord ++ tailWord_745682) baseStart_745682 baseEnd_745682 := by
    simpa [prefixWord, tailWord_745682, baseEnd_745682] using wordTrace_append hprefix tailTrace_745682
  have hstable : (prefixWord ++ tailWord_745682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745682).length < 2 ^ (prefixWord ++ tailWord_745682).sum := by decide
  have hdescent : baseEnd_745682 < baseStart_745682 := by decide
  rcases family_descends (prefixWord ++ tailWord_745682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745705 : List Nat := [1, 2, 1, 1, 1, 2, 2, 8, 5]
def baseStart_745705 : Nat := 118140960795 + 745705 * 2 ^ 59
def prefixEnd_745705 : Nat := 4983230072969 + 3 ^ 40 * 745705 * 2
def baseEnd_745705 : Nat := 42545010162345573273119

theorem tailTrace_745705 : CollatzResearch.WordTrace tailWord_745705 prefixEnd_745705 42545010162345573273119 := by
  unfold tailWord_745705
  simp only [CollatzResearch.WordTrace]
  refine ⟨27198095763445616119758569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18132063842297077413172379 27198095763445616119758569)
  ·
    refine ⟨20398571822584212089818927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27198095763445616119758569 20398571822584212089818927)
    ·
      refine ⟨30597857733876318134728391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20398571822584212089818927 30597857733876318134728391)
      ·
        refine ⟨45896786600814477202092587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30597857733876318134728391 45896786600814477202092587)
        ·
          refine ⟨68845179901221715803138881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45896786600814477202092587 68845179901221715803138881)
          ·
            refine ⟨51633884925916286852354161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68845179901221715803138881 51633884925916286852354161)
            ·
              refine ⟨38725413694437215139265621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51633884925916286852354161 38725413694437215139265621)
              ·
                refine ⟨453813441731686114913269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 38725413694437215139265621 453813441731686114913269)
                ·
                  refine ⟨42545010162345573273119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 453813441731686114913269 42545010162345573273119)
                  ·
                    rfl

theorem cell23_745705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 5].length) (baseStart_745705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745705 prefixEnd_745705 := by exact prefixLift 745705
  have htrace : WordTrace (prefixWord ++ tailWord_745705) baseStart_745705 baseEnd_745705 := by
    simpa [prefixWord, tailWord_745705, baseEnd_745705] using wordTrace_append hprefix tailTrace_745705
  have hstable : (prefixWord ++ tailWord_745705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745705).length < 2 ^ (prefixWord ++ tailWord_745705).sum := by decide
  have hdescent : baseEnd_745705 < baseStart_745705 := by decide
  rcases family_descends (prefixWord ++ tailWord_745705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745715 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 3]
def baseStart_745715 : Nat := 118140960795 + 745715 * 2 ^ 59
def prefixEnd_745715 : Nat := 4983230072969 + 3 ^ 40 * 745715 * 2
def baseEnd_745715 : Nat := 382910226267655120333025

theorem tailTrace_745715 : CollatzResearch.WordTrace tailWord_745715 prefixEnd_745715 382910226267655120333025 := by
  unfold tailWord_745715
  simp only [CollatzResearch.WordTrace]
  refine ⟨27198460493409387827622599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18132306995606258551748399 27198460493409387827622599)
  ·
    refine ⟨40797690740114081741433899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27198460493409387827622599 40797690740114081741433899)
    ·
      refine ⟨61196536110171122612150849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40797690740114081741433899 61196536110171122612150849)
      ·
        refine ⟨45897402082628341959113137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61196536110171122612150849 45897402082628341959113137)
        ·
          refine ⟨34423051561971256469334853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45897402082628341959113137 34423051561971256469334853)
          ·
            refine ⟨6454322167869610588000285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34423051561971256469334853 6454322167869610588000285)
            ·
              refine ⟨2420370812951103970500107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6454322167869610588000285 2420370812951103970500107)
              ·
                refine ⟨3630556219426655955750161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420370812951103970500107 3630556219426655955750161)
                ·
                  refine ⟨2722917164569991966812621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3630556219426655955750161 2722917164569991966812621)
                  ·
                    refine ⟨1021093936713746987554733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722917164569991966812621 1021093936713746987554733)
                    ·
                      refine ⟨382910226267655120333025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1021093936713746987554733 382910226267655120333025)
                      ·
                        rfl

theorem cell23_745715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_745715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745715 prefixEnd_745715 := by exact prefixLift 745715
  have htrace : WordTrace (prefixWord ++ tailWord_745715) baseStart_745715 baseEnd_745715 := by
    simpa [prefixWord, tailWord_745715, baseEnd_745715] using wordTrace_append hprefix tailTrace_745715
  have hstable : (prefixWord ++ tailWord_745715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745715).length < 2 ^ (prefixWord ++ tailWord_745715).sum := by decide
  have hdescent : baseEnd_745715 < baseStart_745715 := by decide
  rcases family_descends (prefixWord ++ tailWord_745715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745728 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_745728 : Nat := 118140960795 + 745728 * 2 ^ 59
def prefixEnd_745728 : Nat := 4983230072969 + 3 ^ 40 * 745728 * 2
def baseEnd_745728 : Nat := 382916901516163569470465

theorem tailTrace_745728 : CollatzResearch.WordTrace tailWord_745728 prefixEnd_745728 382916901516163569470465 := by
  unfold tailWord_745728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599467321181145523922919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18132623094908194031897225 13599467321181145523922919)
  ·
    refine ⟨20399200981771718285884379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13599467321181145523922919 20399200981771718285884379)
    ·
      refine ⟨30598801472657577428826569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20399200981771718285884379 30598801472657577428826569)
      ·
        refine ⟨22949101104493183071619927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30598801472657577428826569 22949101104493183071619927)
        ·
          refine ⟨34423651656739774607429891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22949101104493183071619927 34423651656739774607429891)
          ·
            refine ⟨51635477485109661911144837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34423651656739774607429891 51635477485109661911144837)
            ·
              refine ⟨9681652028458061608339657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51635477485109661911144837 9681652028458061608339657)
              ·
                refine ⟨7261239021343546206254743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9681652028458061608339657 7261239021343546206254743)
                ·
                  refine ⟨10891858532015319309382115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7261239021343546206254743 10891858532015319309382115)
                  ·
                    refine ⟨16337787798022978964073173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10891858532015319309382115 16337787798022978964073173)
                    ·
                      refine ⟨382916901516163569470465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16337787798022978964073173 382916901516163569470465)
                      ·
                        rfl

theorem cell23_745728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_745728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745728 prefixEnd_745728 := by exact prefixLift 745728
  have htrace : WordTrace (prefixWord ++ tailWord_745728) baseStart_745728 baseEnd_745728 := by
    simpa [prefixWord, tailWord_745728, baseEnd_745728] using wordTrace_append hprefix tailTrace_745728
  have hstable : (prefixWord ++ tailWord_745728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745728).length < 2 ^ (prefixWord ++ tailWord_745728).sum := by decide
  have hdescent : baseEnd_745728 < baseStart_745728 := by decide
  rcases family_descends (prefixWord ++ tailWord_745728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745755 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 4]
def baseStart_745755 : Nat := 118140960795 + 745755 * 2 ^ 59
def prefixEnd_745755 : Nat := 4983230072969 + 3 ^ 40 * 745755 * 2
def baseEnd_745755 : Nat := 382930765493834963832841

theorem tailTrace_745755 : CollatzResearch.WordTrace tailWord_745755 prefixEnd_745755 382930765493834963832841 := by
  unfold tailWord_745755
  simp only [CollatzResearch.WordTrace]
  refine ⟨27199919413264474659078719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18133279608842983106052479 27199919413264474659078719)
  ·
    refine ⟨40799879119896711988618079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27199919413264474659078719 40799879119896711988618079)
    ·
      refine ⟨61199818679845067982927119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40799879119896711988618079 61199818679845067982927119)
      ·
        refine ⟨91799728019767601974390679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61199818679845067982927119 91799728019767601974390679)
        ·
          refine ⟨137699592029651402961586019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91799728019767601974390679 137699592029651402961586019)
          ·
            refine ⟨206549388044477104442379029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137699592029651402961586019 206549388044477104442379029)
            ·
              refine ⟨9682002564584864270736517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 206549388044477104442379029 9682002564584864270736517)
              ·
                refine ⟨1815375480859662050763097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9682002564584864270736517 1815375480859662050763097)
                ·
                  refine ⟨1361531610644746538072323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1815375480859662050763097 1361531610644746538072323)
                  ·
                    refine ⟨2042297415967119807108485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1361531610644746538072323 2042297415967119807108485)
                    ·
                      refine ⟨382930765493834963832841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2042297415967119807108485 382930765493834963832841)
                      ·
                        rfl

theorem cell23_745755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 4].length) (baseStart_745755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745755 prefixEnd_745755 := by exact prefixLift 745755
  have htrace : WordTrace (prefixWord ++ tailWord_745755) baseStart_745755 baseEnd_745755 := by
    simpa [prefixWord, tailWord_745755, baseEnd_745755] using wordTrace_append hprefix tailTrace_745755
  have hstable : (prefixWord ++ tailWord_745755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745755).length < 2 ^ (prefixWord ++ tailWord_745755).sum := by decide
  have hdescent : baseEnd_745755 < baseStart_745755 := by decide
  rcases family_descends (prefixWord ++ tailWord_745755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745767 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_745767 : Nat := 118140960795 + 745767 * 2 ^ 59
def prefixEnd_745767 : Nat := 4983230072969 + 3 ^ 40 * 745767 * 2
def baseEnd_745767 : Nat := 382936927261688916882787

theorem tailTrace_745767 : CollatzResearch.WordTrace tailWord_745767 prefixEnd_745767 382936927261688916882787 := by
  unfold tailWord_745767
  simp only [CollatzResearch.WordTrace]
  refine ⟨27200357089221000708515555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18133571392814000472343703 27200357089221000708515555)
  ·
    refine ⟨40800535633831501062773333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27200357089221000708515555 40800535633831501062773333)
    ·
      refine ⟨478131276958962903079375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 40800535633831501062773333 478131276958962903079375)
      ·
        refine ⟨717196915438444354619063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478131276958962903079375 717196915438444354619063)
        ·
          refine ⟨1075795373157666531928595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717196915438444354619063 1075795373157666531928595)
          ·
            refine ⟨1613693059736499797892893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075795373157666531928595 1613693059736499797892893)
            ·
              refine ⟨605134897401187424209835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1613693059736499797892893 605134897401187424209835)
              ·
                refine ⟨907702346101781136314753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605134897401187424209835 907702346101781136314753)
                ·
                  refine ⟨680776759576335852236065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 907702346101781136314753 680776759576335852236065)
                  ·
                    refine ⟨510582569682251889177049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 680776759576335852236065 510582569682251889177049)
                    ·
                      refine ⟨382936927261688916882787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510582569682251889177049 382936927261688916882787)
                      ·
                        rfl

theorem cell23_745767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_745767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745767 prefixEnd_745767 := by exact prefixLift 745767
  have htrace : WordTrace (prefixWord ++ tailWord_745767) baseStart_745767 baseEnd_745767 := by
    simpa [prefixWord, tailWord_745767, baseEnd_745767] using wordTrace_append hprefix tailTrace_745767
  have hstable : (prefixWord ++ tailWord_745767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745767).length < 2 ^ (prefixWord ++ tailWord_745767).sum := by decide
  have hdescent : baseEnd_745767 < baseStart_745767 := by decide
  rcases family_descends (prefixWord ++ tailWord_745767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745772 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 2, 4, 2]
def baseStart_745772 : Nat := 118140960795 + 745772 * 2 ^ 59
def prefixEnd_745772 : Nat := 4983230072969 + 3 ^ 40 * 745772 * 2
def baseEnd_745772 : Nat := 382939494664961397320263

theorem tailTrace_745772 : CollatzResearch.WordTrace tailWord_745772 prefixEnd_745772 382939494664961397320263 := by
  unfold tailWord_745772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13600269727101443281223785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18133692969468591041631713 13600269727101443281223785)
  ·
    refine ⟨10200202295326082460917839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13600269727101443281223785 10200202295326082460917839)
    ·
      refine ⟨15300303442989123691376759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200202295326082460917839 15300303442989123691376759)
      ·
        refine ⟨22950455164483685537065139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15300303442989123691376759 22950455164483685537065139)
        ·
          refine ⟨34425682746725528305597709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22950455164483685537065139 34425682746725528305597709)
          ·
            refine ⟨12909631030022073114599141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34425682746725528305597709 12909631030022073114599141)
            ·
              refine ⟨2420555818129138708987339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12909631030022073114599141 2420555818129138708987339)
              ·
                refine ⟨3630833727193708063481009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420555818129138708987339 3630833727193708063481009)
                ·
                  refine ⟨2723125295395281047610757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3630833727193708063481009 2723125295395281047610757)
                  ·
                    refine ⟨510585992886615196427017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2723125295395281047610757 510585992886615196427017)
                    ·
                      refine ⟨382939494664961397320263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510585992886615196427017 382939494664961397320263)
                      ·
                        rfl

theorem cell23_745772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_745772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745772 prefixEnd_745772 := by exact prefixLift 745772
  have htrace : WordTrace (prefixWord ++ tailWord_745772) baseStart_745772 baseEnd_745772 := by
    simpa [prefixWord, tailWord_745772, baseEnd_745772] using wordTrace_append hprefix tailTrace_745772
  have hstable : (prefixWord ++ tailWord_745772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745772).length < 2 ^ (prefixWord ++ tailWord_745772).sum := by decide
  have hdescent : baseEnd_745772 < baseStart_745772 := by decide
  rcases family_descends (prefixWord ++ tailWord_745772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745775 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 3]
def baseStart_745775 : Nat := 118140960795 + 745775 * 2 ^ 59
def prefixEnd_745775 : Nat := 4983230072969 + 3 ^ 40 * 745775 * 2
def baseEnd_745775 : Nat := 382941035106924885582749

theorem tailTrace_745775 : CollatzResearch.WordTrace tailWord_745775 prefixEnd_745775 382941035106924885582749 := by
  unfold tailWord_745775
  simp only [CollatzResearch.WordTrace]
  refine ⟨27200648873192018074806779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18133765915461345383204519 27200648873192018074806779)
  ·
    refine ⟨40800973309788027112210169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27200648873192018074806779 40800973309788027112210169)
    ·
      refine ⟨30600729982341020334157627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40800973309788027112210169 30600729982341020334157627)
      ·
        refine ⟨45901094973511530501236441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30600729982341020334157627 45901094973511530501236441)
        ·
          refine ⟨34425821230133647875927331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45901094973511530501236441 34425821230133647875927331)
          ·
            refine ⟨51638731845200471813890997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34425821230133647875927331 51638731845200471813890997)
            ·
              refine ⟨4841131110487544232552281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51638731845200471813890997 4841131110487544232552281)
              ·
                refine ⟨3630848332865658174414211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4841131110487544232552281 3630848332865658174414211)
                ·
                  refine ⟨5446272499298487261621317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630848332865658174414211 5446272499298487261621317)
                  ·
                    refine ⟨1021176093618466361553997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446272499298487261621317 1021176093618466361553997)
                    ·
                      refine ⟨382941035106924885582749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1021176093618466361553997 382941035106924885582749)
                      ·
                        rfl

theorem cell23_745775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_745775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745775 prefixEnd_745775 := by exact prefixLift 745775
  have htrace : WordTrace (prefixWord ++ tailWord_745775) baseStart_745775 baseEnd_745775 := by
    simpa [prefixWord, tailWord_745775, baseEnd_745775] using wordTrace_append hprefix tailTrace_745775
  have hstable : (prefixWord ++ tailWord_745775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745775).length < 2 ^ (prefixWord ++ tailWord_745775).sum := by decide
  have hdescent : baseEnd_745775 < baseStart_745775 := by decide
  rcases family_descends (prefixWord ++ tailWord_745775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745829 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 6]
def baseStart_745829 : Nat := 118140960795 + 745829 * 2 ^ 59
def prefixEnd_745829 : Nat := 4983230072969 + 3 ^ 40 * 745829 * 2
def baseEnd_745829 : Nat := 42552084784696408256389

theorem tailTrace_745829 : CollatzResearch.WordTrace tailWord_745829 prefixEnd_745829 42552084784696408256389 := by
  unfold tailWord_745829
  simp only [CollatzResearch.WordTrace]
  refine ⟨27202618414996385297272541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18135078943330923531515027 27202618414996385297272541)
  ·
    refine ⟨10200981905623644486477203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27202618414996385297272541 10200981905623644486477203)
    ·
      refine ⟨15301472858435466729715805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200981905623644486477203 15301472858435466729715805)
      ·
        refine ⟨5738052321913300023643427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15301472858435466729715805 5738052321913300023643427)
        ·
          refine ⟨8607078482869950035465141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5738052321913300023643427 8607078482869950035465141)
          ·
            refine ⟨806913607769057815824857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8607078482869950035465141 806913607769057815824857)
            ·
              refine ⟨605185205826793361868643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806913607769057815824857 605185205826793361868643)
              ·
                refine ⟨907777808740190042802965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605185205826793361868643 907777808740190042802965)
                ·
                  refine ⟨42552084784696408256389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 907777808740190042802965 42552084784696408256389)
                  ·
                    rfl

theorem cell23_745829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_745829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745829 prefixEnd_745829 := by exact prefixLift 745829
  have htrace : WordTrace (prefixWord ++ tailWord_745829) baseStart_745829 baseEnd_745829 := by
    simpa [prefixWord, tailWord_745829, baseEnd_745829] using wordTrace_append hprefix tailTrace_745829
  have hstable : (prefixWord ++ tailWord_745829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745829).length < 2 ^ (prefixWord ++ tailWord_745829).sum := by decide
  have hdescent : baseEnd_745829 < baseStart_745829 := by decide
  rcases family_descends (prefixWord ++ tailWord_745829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745842 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_745842 : Nat := 118140960795 + 745842 * 2 ^ 59
def prefixEnd_745842 : Nat := 4983230072969 + 3 ^ 40 * 745842 * 2
def baseEnd_745842 : Nat := 127658479436925374481647

theorem tailTrace_745842 : CollatzResearch.WordTrace tailWord_745842 prefixEnd_745842 127658479436925374481647 := by
  unfold tailWord_745842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800773140987322129373945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18135395042632859011663853 6800773140987322129373945)
  ·
    refine ⟨5100579855740491597030459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6800773140987322129373945 5100579855740491597030459)
    ·
      refine ⟨7650869783610737395545689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100579855740491597030459 7650869783610737395545689)
      ·
        refine ⟨5738152337708053046659267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7650869783610737395545689 5738152337708053046659267)
        ·
          refine ⟨8607228506562079569988901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5738152337708053046659267 8607228506562079569988901)
          ·
            refine ⟨1613855344980389919372919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8607228506562079569988901 1613855344980389919372919)
            ·
              refine ⟨2420783017470584879059379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613855344980389919372919 2420783017470584879059379)
              ·
                refine ⟨3631174526205877318589069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420783017470584879059379 3631174526205877318589069)
                ·
                  refine ⟨1361690447327203994470901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3631174526205877318589069 1361690447327203994470901)
                  ·
                    refine ⟨127658479436925374481647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1361690447327203994470901 127658479436925374481647)
                    ·
                      rfl

theorem cell23_745842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_745842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745842 prefixEnd_745842 := by exact prefixLift 745842
  have htrace : WordTrace (prefixWord ++ tailWord_745842) baseStart_745842 baseEnd_745842 := by
    simpa [prefixWord, tailWord_745842, baseEnd_745842] using wordTrace_append hprefix tailTrace_745842
  have hstable : (prefixWord ++ tailWord_745842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745842).length < 2 ^ (prefixWord ++ tailWord_745842).sum := by decide
  have hdescent : baseEnd_745842 < baseStart_745842 := by decide
  rcases family_descends (prefixWord ++ tailWord_745842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745855 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 1, 6]
def baseStart_745855 : Nat := 118140960795 + 745855 * 2 ^ 59
def prefixEnd_745855 : Nat := 4983230072969 + 3 ^ 40 * 745855 * 2
def baseEnd_745855 : Nat := 127660704519761524194127

theorem tailTrace_745855 : CollatzResearch.WordTrace tailWord_745855 prefixEnd_745855 127660704519761524194127 := by
  unfold tailWord_745855
  simp only [CollatzResearch.WordTrace]
  refine ⟨27203566712902191737719019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18135711141934794491812679 27203566712902191737719019)
  ·
    refine ⟨40805350069353287606578529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27203566712902191737719019 40805350069353287606578529)
    ·
      refine ⟨30604012552014965704933897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40805350069353287606578529 30604012552014965704933897)
      ·
        refine ⟨22953009414011224278700423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30604012552014965704933897 22953009414011224278700423)
        ·
          refine ⟨34429514121016836418050635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22953009414011224278700423 34429514121016836418050635)
          ·
            refine ⟨51644271181525254627075953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34429514121016836418050635 51644271181525254627075953)
            ·
              refine ⟨38733203386143940970306965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51644271181525254627075953 38733203386143940970306965)
              ·
                refine ⟨1815618908725497232983139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38733203386143940970306965 1815618908725497232983139)
                ·
                  refine ⟨2723428363088245849474709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815618908725497232983139 2723428363088245849474709)
                  ·
                    refine ⟨127660704519761524194127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2723428363088245849474709 127660704519761524194127)
                    ·
                      rfl

theorem cell23_745855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_745855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745855 prefixEnd_745855 := by exact prefixLift 745855
  have htrace : WordTrace (prefixWord ++ tailWord_745855) baseStart_745855 baseEnd_745855 := by
    simpa [prefixWord, tailWord_745855, baseEnd_745855] using wordTrace_append hprefix tailTrace_745855
  have hstable : (prefixWord ++ tailWord_745855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745855).length < 2 ^ (prefixWord ++ tailWord_745855).sum := by decide
  have hdescent : baseEnd_745855 < baseStart_745855 := by decide
  rcases family_descends (prefixWord ++ tailWord_745855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745892 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_745892 : Nat := 118140960795 + 745892 * 2 ^ 59
def prefixEnd_745892 : Nat := 4983230072969 + 3 ^ 40 * 745892 * 2
def baseEnd_745892 : Nat := 383001112343500927819711

theorem tailTrace_745892 : CollatzResearch.WordTrace tailWord_745892 prefixEnd_745892 383001112343500927819711 := by
  unfold tailWord_745892
  simp only [CollatzResearch.WordTrace]
  refine ⟨13602458106884073528407965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18136610809178764704543953 13602458106884073528407965)
  ·
    refine ⟨5100921790081527573152987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13602458106884073528407965 5100921790081527573152987)
    ·
      refine ⟨7651382685122291359729481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100921790081527573152987 7651382685122291359729481)
      ·
        refine ⟨5738537013841718519797111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7651382685122291359729481 5738537013841718519797111)
        ·
          refine ⟨8607805520762577779695667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5738537013841718519797111 8607805520762577779695667)
          ·
            refine ⟨12911708281143866669543501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8607805520762577779695667 12911708281143866669543501)
            ·
              refine ⟨4841890605428950001078813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12911708281143866669543501 4841890605428950001078813)
              ·
                refine ⟨1815708977035856250404555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4841890605428950001078813 1815708977035856250404555)
                ·
                  refine ⟨2723563465553784375606833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815708977035856250404555 2723563465553784375606833)
                  ·
                    refine ⟨2042672599165338281705125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2723563465553784375606833 2042672599165338281705125)
                    ·
                      refine ⟨383001112343500927819711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2042672599165338281705125 383001112343500927819711)
                      ·
                        rfl

theorem cell23_745892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_745892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745892 prefixEnd_745892 := by exact prefixLift 745892
  have htrace : WordTrace (prefixWord ++ tailWord_745892) baseStart_745892 baseEnd_745892 := by
    simpa [prefixWord, tailWord_745892, baseEnd_745892] using wordTrace_append hprefix tailTrace_745892
  have hstable : (prefixWord ++ tailWord_745892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745892).length < 2 ^ (prefixWord ++ tailWord_745892).sum := by decide
  have hdescent : baseEnd_745892 < baseStart_745892 := by decide
  rcases family_descends (prefixWord ++ tailWord_745892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745913 : List Nat := [1, 2, 1, 4, 3, 1, 1, 5, 1, 2, 2]
def baseStart_745913 : Nat := 118140960795 + 745913 * 2 ^ 59
def prefixEnd_745913 : Nat := 4983230072969 + 3 ^ 40 * 745913 * 2
def baseEnd_745913 : Nat := 383011895437245345657115

theorem tailTrace_745913 : CollatzResearch.WordTrace tailWord_745913 prefixEnd_745913 383011895437245345657115 := by
  unfold tailWord_745913
  simp only [CollatzResearch.WordTrace]
  refine ⟨27205682146692067643330393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18137121431128045095553595 27205682146692067643330393)
  ·
    refine ⟨20404261610019050732497795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27205682146692067643330393 20404261610019050732497795)
    ·
      refine ⟨30606392415028576098746693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20404261610019050732497795 30606392415028576098746693)
      ·
        refine ⟨5738698577817858018515005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30606392415028576098746693 5738698577817858018515005)
        ·
          refine ⟨2152011966681696756943127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5738698577817858018515005 2152011966681696756943127)
          ·
            refine ⟨3228017950022545135414691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152011966681696756943127 3228017950022545135414691)
            ·
              refine ⟨4842026925033817703122037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228017950022545135414691 4842026925033817703122037)
              ·
                refine ⟨453940024221920409667691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4842026925033817703122037 453940024221920409667691)
                ·
                  refine ⟨680910036332880614501537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 453940024221920409667691 680910036332880614501537)
                  ·
                    refine ⟨510682527249660460876153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 680910036332880614501537 510682527249660460876153)
                    ·
                      refine ⟨383011895437245345657115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510682527249660460876153 383011895437245345657115)
                      ·
                        rfl

theorem cell23_745913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_745913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745913 prefixEnd_745913 := by exact prefixLift 745913
  have htrace : WordTrace (prefixWord ++ tailWord_745913) baseStart_745913 baseEnd_745913 := by
    simpa [prefixWord, tailWord_745913, baseEnd_745913] using wordTrace_append hprefix tailTrace_745913
  have hstable : (prefixWord ++ tailWord_745913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745913).length < 2 ^ (prefixWord ++ tailWord_745913).sum := by decide
  have hdescent : baseEnd_745913 < baseStart_745913 := by decide
  rcases family_descends (prefixWord ++ tailWord_745913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745916 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_745916 : Nat := 118140960795 + 745916 * 2 ^ 59
def prefixEnd_745916 : Nat := 4983230072969 + 3 ^ 40 * 745916 * 2
def baseEnd_745916 : Nat := 383013435879208833919601

theorem tailTrace_745916 : CollatzResearch.WordTrace tailWord_745916 prefixEnd_745916 383013435879208833919601 := by
  unfold tailWord_745916
  simp only [CollatzResearch.WordTrace]
  refine ⟨13602895782840599577844801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18137194377120799437126401 13602895782840599577844801)
  ·
    refine ⟨10202171837130449683383601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13602895782840599577844801 10202171837130449683383601)
    ·
      refine ⟨7651628877847837262537701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10202171837130449683383601 7651628877847837262537701)
      ·
        refine ⟨1434680414596469486725819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7651628877847837262537701 1434680414596469486725819)
        ·
          refine ⟨2152020621894704230088729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434680414596469486725819 2152020621894704230088729)
          ·
            refine ⟨1614015466421028172566547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2152020621894704230088729 1614015466421028172566547)
            ·
              refine ⟨2421023199631542258849821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614015466421028172566547 2421023199631542258849821)
              ·
                refine ⟨907883699861828347068683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2421023199631542258849821 907883699861828347068683)
                ·
                  refine ⟨1361825549792742520603025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907883699861828347068683 1361825549792742520603025)
                  ·
                    refine ⟨1021369162344556890452269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1361825549792742520603025 1021369162344556890452269)
                    ·
                      refine ⟨383013435879208833919601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1021369162344556890452269 383013435879208833919601)
                      ·
                        rfl

theorem cell23_745916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_745916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745916 prefixEnd_745916 := by exact prefixLift 745916
  have htrace : WordTrace (prefixWord ++ tailWord_745916) baseStart_745916 baseEnd_745916 := by
    simpa [prefixWord, tailWord_745916, baseEnd_745916] using wordTrace_append hprefix tailTrace_745916
  have hstable : (prefixWord ++ tailWord_745916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745916).length < 2 ^ (prefixWord ++ tailWord_745916).sum := by decide
  have hdescent : baseEnd_745916 < baseStart_745916 := by decide
  rcases family_descends (prefixWord ++ tailWord_745916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745969 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 3, 4, 2]
def baseStart_745969 : Nat := 118140960795 + 745969 * 2 ^ 59
def prefixEnd_745969 : Nat := 4983230072969 + 3 ^ 40 * 745969 * 2
def baseEnd_745969 : Nat := 383040650353897126556857

theorem tailTrace_745969 : CollatzResearch.WordTrace tailWord_745969 prefixEnd_745969 383040650353897126556857 := by
  unfold tailWord_745969
  simp only [CollatzResearch.WordTrace]
  refine ⟨27207724634489189207368961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18138483089659459471579307 27207724634489189207368961)
  ·
    refine ⟨20405793475866891905526721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27207724634489189207368961 20405793475866891905526721)
    ·
      refine ⟨15304345106900168929145041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20405793475866891905526721 15304345106900168929145041)
      ·
        refine ⟨11478258830175126696858781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15304345106900168929145041 11478258830175126696858781)
        ·
          refine ⟨4304347061315672511322043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11478258830175126696858781 4304347061315672511322043)
          ·
            refine ⟨6456520591973508766983065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304347061315672511322043 6456520591973508766983065)
            ·
              refine ⟨4842390443980131575237299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6456520591973508766983065 4842390443980131575237299)
              ·
                refine ⟨7263585665970197362855949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842390443980131575237299 7263585665970197362855949)
                ·
                  refine ⟨2723844624738824011070981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7263585665970197362855949 2723844624738824011070981)
                  ·
                    refine ⟨510720867138529502075809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2723844624738824011070981 510720867138529502075809)
                    ·
                      refine ⟨383040650353897126556857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510720867138529502075809 383040650353897126556857)
                      ·
                        rfl

theorem cell23_745969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_745969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745969 prefixEnd_745969 := by exact prefixLift 745969
  have htrace : WordTrace (prefixWord ++ tailWord_745969) baseStart_745969 baseEnd_745969 := by
    simpa [prefixWord, tailWord_745969, baseEnd_745969] using wordTrace_append hprefix tailTrace_745969
  have hstable : (prefixWord ++ tailWord_745969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745969).length < 2 ^ (prefixWord ++ tailWord_745969).sum := by decide
  have hdescent : baseEnd_745969 < baseStart_745969 := by decide
  rcases family_descends (prefixWord ++ tailWord_745969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745997 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_745997 : Nat := 118140960795 + 745997 * 2 ^ 59
def prefixEnd_745997 : Nat := 4983230072969 + 3 ^ 40 * 745997 * 2
def baseEnd_745997 : Nat := 383055027812223017006729

theorem tailTrace_745997 : CollatzResearch.WordTrace tailWord_745997 prefixEnd_745997 383055027812223017006729 := by
  unfold tailWord_745997
  simp only [CollatzResearch.WordTrace]
  refine ⟨27208745878387749989388245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18139163918925166659592163 27208745878387749989388245)
  ·
    refine ⟨637704981524712890376287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27208745878387749989388245 637704981524712890376287)
    ·
      refine ⟨956557472287069335564431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 637704981524712890376287 956557472287069335564431)
      ·
        refine ⟨1434836208430604003346647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956557472287069335564431 1434836208430604003346647)
        ·
          refine ⟨2152254312645906005019971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434836208430604003346647 2152254312645906005019971)
          ·
            refine ⟨3228381468968859007529957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152254312645906005019971 3228381468968859007529957)
            ·
              refine ⟨605321525431661063911867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3228381468968859007529957 605321525431661063911867)
              ·
                refine ⟨907982288147491595867801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605321525431661063911867 907982288147491595867801)
                ·
                  refine ⟨680986716110618696900851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 907982288147491595867801 680986716110618696900851)
                  ·
                    refine ⟨1021480074165928045351277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 680986716110618696900851 1021480074165928045351277)
                    ·
                      refine ⟨383055027812223017006729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1021480074165928045351277 383055027812223017006729)
                      ·
                        rfl

theorem cell23_745997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_745997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_745997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_745997 prefixEnd_745997 := by exact prefixLift 745997
  have htrace : WordTrace (prefixWord ++ tailWord_745997) baseStart_745997 baseEnd_745997 := by
    simpa [prefixWord, tailWord_745997, baseEnd_745997] using wordTrace_append hprefix tailTrace_745997
  have hstable : (prefixWord ++ tailWord_745997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745997).length < 2 ^ (prefixWord ++ tailWord_745997).sum := by decide
  have hdescent : baseEnd_745997 < baseStart_745997 := by decide
  rcases family_descends (prefixWord ++ tailWord_745997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746007 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 1, 3, 2]
def baseStart_746007 : Nat := 118140960795 + 746007 * 2 ^ 59
def prefixEnd_746007 : Nat := 4983230072969 + 3 ^ 40 * 746007 * 2
def baseEnd_746007 : Nat := 383060162618767977881683

theorem tailTrace_746007 : CollatzResearch.WordTrace tailWord_746007 prefixEnd_746007 383060162618767977881683 := by
  unfold tailWord_746007
  simp only [CollatzResearch.WordTrace]
  refine ⟨27209110608351521697252275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18139407072234347798168183 27209110608351521697252275)
  ·
    refine ⟨40813665912527282545878413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27209110608351521697252275 40813665912527282545878413)
    ·
      refine ⟨15305124717197730954704405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40813665912527282545878413 15305124717197730954704405)
      ·
        refine ⟨717427721118643638501769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15305124717197730954704405 717427721118643638501769)
        ·
          refine ⟨538070790838982728876327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717427721118643638501769 538070790838982728876327)
          ·
            refine ⟨807106186258474093314491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538070790838982728876327 807106186258474093314491)
            ·
              refine ⟨1210659279387711139971737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807106186258474093314491 1210659279387711139971737)
              ·
                refine ⟨907994459540783354978803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210659279387711139971737 907994459540783354978803)
                ·
                  refine ⟨1361991689311175032468205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907994459540783354978803 1361991689311175032468205)
                  ·
                    refine ⟨510746883491690637175577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1361991689311175032468205 510746883491690637175577)
                    ·
                      refine ⟨383060162618767977881683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510746883491690637175577 383060162618767977881683)
                      ·
                        rfl

theorem cell23_746007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_746007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746007 prefixEnd_746007 := by exact prefixLift 746007
  have htrace : WordTrace (prefixWord ++ tailWord_746007) baseStart_746007 baseEnd_746007 := by
    simpa [prefixWord, tailWord_746007, baseEnd_746007] using wordTrace_append hprefix tailTrace_746007
  have hstable : (prefixWord ++ tailWord_746007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746007).length < 2 ^ (prefixWord ++ tailWord_746007).sum := by decide
  have hdescent : baseEnd_746007 < baseStart_746007 := by decide
  rcases family_descends (prefixWord ++ tailWord_746007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746032 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_746032 : Nat := 118140960795 + 746032 * 2 ^ 59
def prefixEnd_746032 : Nat := 4983230072969 + 3 ^ 40 * 746032 * 2
def baseEnd_746032 : Nat := 383072999635130380069067

theorem tailTrace_746032 : CollatzResearch.WordTrace tailWord_746032 prefixEnd_746032 383072999635130380069067 := by
  unfold tailWord_746032
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605011216630475483456175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18140014955507300644608233 13605011216630475483456175)
  ·
    refine ⟨20407516824945713225184263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13605011216630475483456175 20407516824945713225184263)
    ·
      refine ⟨30611275237418569837776395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20407516824945713225184263 30611275237418569837776395)
      ·
        refine ⟨45916912856127854756664593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30611275237418569837776395 45916912856127854756664593)
        ·
          refine ⟨34437684642095891067498445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45916912856127854756664593 34437684642095891067498445)
          ·
            refine ⟨12914131740785959150311917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34437684642095891067498445 12914131740785959150311917)
            ·
              refine ⟨4842799402794734681366969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12914131740785959150311917 4842799402794734681366969)
              ·
                refine ⟨3632099552096051011025227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842799402794734681366969 3632099552096051011025227)
                ·
                  refine ⟨5448149328144076516537841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632099552096051011025227 5448149328144076516537841)
                  ·
                    refine ⟨4086111996108057387403381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448149328144076516537841 4086111996108057387403381)
                    ·
                      refine ⟨383072999635130380069067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4086111996108057387403381 383072999635130380069067)
                      ·
                        rfl

theorem cell23_746032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_746032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746032 prefixEnd_746032 := by exact prefixLift 746032
  have htrace : WordTrace (prefixWord ++ tailWord_746032) baseStart_746032 baseEnd_746032 := by
    simpa [prefixWord, tailWord_746032, baseEnd_746032] using wordTrace_append hprefix tailTrace_746032
  have hstable : (prefixWord ++ tailWord_746032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746032).length < 2 ^ (prefixWord ++ tailWord_746032).sum := by decide
  have hdescent : baseEnd_746032 < baseStart_746032 := by decide
  rcases family_descends (prefixWord ++ tailWord_746032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746049 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_746049 : Nat := 118140960795 + 746049 * 2 ^ 59
def prefixEnd_746049 : Nat := 4983230072969 + 3 ^ 40 * 746049 * 2
def baseEnd_746049 : Nat := 383081728806256813556489

theorem tailTrace_746049 : CollatzResearch.WordTrace tailWord_746049 prefixEnd_746049 383081728806256813556489 := by
  unfold tailWord_746049
  simp only [CollatzResearch.WordTrace]
  refine ⟨27210642474199362870281201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18140428316132908580187467 27210642474199362870281201)
  ·
    refine ⟨20407981855649522152710901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27210642474199362870281201 20407981855649522152710901)
    ·
      refine ⟨1913248298967142701816647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20407981855649522152710901 1913248298967142701816647)
      ·
        refine ⟨2869872448450714052724971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913248298967142701816647 2869872448450714052724971)
        ·
          refine ⟨4304808672676071079087457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869872448450714052724971 4304808672676071079087457)
          ·
            refine ⟨3228606504507053309315593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4304808672676071079087457 3228606504507053309315593)
            ·
              refine ⟨2421454878380289981986695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228606504507053309315593 2421454878380289981986695)
              ·
                refine ⟨3632182317570434972980043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421454878380289981986695 3632182317570434972980043)
                ·
                  refine ⟨5448273476355652459470065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632182317570434972980043 5448273476355652459470065)
                  ·
                    refine ⟨4086205107266739344602549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448273476355652459470065 4086205107266739344602549)
                    ·
                      refine ⟨383081728806256813556489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4086205107266739344602549 383081728806256813556489)
                      ·
                        rfl

theorem cell23_746049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_746049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746049 prefixEnd_746049 := by exact prefixLift 746049
  have htrace : WordTrace (prefixWord ++ tailWord_746049) baseStart_746049 baseEnd_746049 := by
    simpa [prefixWord, tailWord_746049, baseEnd_746049] using wordTrace_append hprefix tailTrace_746049
  have hstable : (prefixWord ++ tailWord_746049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746049).length < 2 ^ (prefixWord ++ tailWord_746049).sum := by decide
  have hdescent : baseEnd_746049 < baseStart_746049 := by decide
  rcases family_descends (prefixWord ++ tailWord_746049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746059 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 1, 6, 2]
def baseStart_746059 : Nat := 118140960795 + 746059 * 2 ^ 59
def prefixEnd_746059 : Nat := 4983230072969 + 3 ^ 40 * 746059 * 2
def baseEnd_746059 : Nat := 383086863612801774431443

theorem tailTrace_746059 : CollatzResearch.WordTrace tailWord_746059 prefixEnd_746059 383086863612801774431443 := by
  unfold tailWord_746059
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211007204163134578145231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18140671469442089718763487 27211007204163134578145231)
  ·
    refine ⟨40816510806244701867217847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27211007204163134578145231 40816510806244701867217847)
    ·
      refine ⟨61224766209367052800826771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40816510806244701867217847 61224766209367052800826771)
      ·
        refine ⟨91837149314050579201240157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61224766209367052800826771 91837149314050579201240157)
        ·
          refine ⟨34438930992768967200465059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91837149314050579201240157 34438930992768967200465059)
          ·
            refine ⟨51658396489153450800697589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34438930992768967200465059 51658396489153450800697589)
            ·
              refine ⟨4842974670858136012565399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51658396489153450800697589 4842974670858136012565399)
              ·
                refine ⟨7264462006287204018848099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842974670858136012565399 7264462006287204018848099)
                ·
                  refine ⟨10896693009430806028272149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7264462006287204018848099 10896693009430806028272149)
                  ·
                    refine ⟨510782484817069032575257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10896693009430806028272149 510782484817069032575257)
                    ·
                      refine ⟨383086863612801774431443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510782484817069032575257 383086863612801774431443)
                      ·
                        rfl

theorem cell23_746059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 6, 2].length) (baseStart_746059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746059 prefixEnd_746059 := by exact prefixLift 746059
  have htrace : WordTrace (prefixWord ++ tailWord_746059) baseStart_746059 baseEnd_746059 := by
    simpa [prefixWord, tailWord_746059, baseEnd_746059] using wordTrace_append hprefix tailTrace_746059
  have hstable : (prefixWord ++ tailWord_746059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746059).length < 2 ^ (prefixWord ++ tailWord_746059).sum := by decide
  have hdescent : baseEnd_746059 < baseStart_746059 := by decide
  rcases family_descends (prefixWord ++ tailWord_746059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746069 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_746069 : Nat := 118140960795 + 746069 * 2 ^ 59
def prefixEnd_746069 : Nat := 4983230072969 + 3 ^ 40 * 746069 * 2
def baseEnd_746069 : Nat := 127697332806448911768799

theorem tailTrace_746069 : CollatzResearch.WordTrace tailWord_746069 prefixEnd_746069 127697332806448911768799 := by
  unfold tailWord_746069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211371934126906286009261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18140914622751270857339507 27211371934126906286009261)
  ·
    refine ⟨10204264475297589857253473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27211371934126906286009261 10204264475297589857253473)
    ·
      refine ⟨7653198356473192392940105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10204264475297589857253473 7653198356473192392940105)
      ·
        refine ⟨5739898767354894294705079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7653198356473192392940105 5739898767354894294705079)
        ·
          refine ⟨8609848151032341442057619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739898767354894294705079 8609848151032341442057619)
          ·
            refine ⟨12914772226548512163086429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609848151032341442057619 12914772226548512163086429)
            ·
              refine ⟨4843039584955692061157411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12914772226548512163086429 4843039584955692061157411)
              ·
                refine ⟨7264559377433538091736117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4843039584955692061157411 7264559377433538091736117)
                ·
                  refine ⟨681052441634394196100261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7264559377433538091736117 681052441634394196100261)
                  ·
                    refine ⟨127697332806448911768799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681052441634394196100261 127697332806448911768799)
                    ·
                      rfl

theorem cell23_746069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_746069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746069 prefixEnd_746069 := by exact prefixLift 746069
  have htrace : WordTrace (prefixWord ++ tailWord_746069) baseStart_746069 baseEnd_746069 := by
    simpa [prefixWord, tailWord_746069, baseEnd_746069] using wordTrace_append hprefix tailTrace_746069
  have hstable : (prefixWord ++ tailWord_746069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746069).length < 2 ^ (prefixWord ++ tailWord_746069).sum := by decide
  have hdescent : baseEnd_746069 < baseStart_746069 := by decide
  rcases family_descends (prefixWord ++ tailWord_746069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746076 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_746076 : Nat := 118140960795 + 746076 * 2 ^ 59
def prefixEnd_746076 : Nat := 4983230072969 + 3 ^ 40 * 746076 * 2
def baseEnd_746076 : Nat := 383095592783928207918865

theorem tailTrace_746076 : CollatzResearch.WordTrace tailWord_746076 prefixEnd_746076 383095592783928207918865 := by
  unfold tailWord_746076
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605813622550773240757041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18141084830067697654342721 13605813622550773240757041)
  ·
    refine ⟨10204360216913079930567781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13605813622550773240757041 10204360216913079930567781)
    ·
      refine ⟨1913317540671202486981459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10204360216913079930567781 1913317540671202486981459)
      ·
        refine ⟨2869976311006803730472189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913317540671202486981459 2869976311006803730472189)
        ·
          refine ⟨1076241116627551398927071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2869976311006803730472189 1076241116627551398927071)
          ·
            refine ⟨1614361674941327098390607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076241116627551398927071 1614361674941327098390607)
            ·
              refine ⟨2421542512411990647585911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614361674941327098390607 2421542512411990647585911)
              ·
                refine ⟨3632313768617985971378867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421542512411990647585911 3632313768617985971378867)
                ·
                  refine ⟨5448470652926978957068301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632313768617985971378867 5448470652926978957068301)
                  ·
                    refine ⟨2043176494847617108900613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5448470652926978957068301 2043176494847617108900613)
                    ·
                      refine ⟨383095592783928207918865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2043176494847617108900613 383095592783928207918865)
                      ·
                        rfl

theorem cell23_746076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_746076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746076 prefixEnd_746076 := by exact prefixLift 746076
  have htrace : WordTrace (prefixWord ++ tailWord_746076) baseStart_746076 baseEnd_746076 := by
    simpa [prefixWord, tailWord_746076, baseEnd_746076] using wordTrace_append hprefix tailTrace_746076
  have hstable : (prefixWord ++ tailWord_746076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746076).length < 2 ^ (prefixWord ++ tailWord_746076).sum := by decide
  have hdescent : baseEnd_746076 < baseStart_746076 := by decide
  rcases family_descends (prefixWord ++ tailWord_746076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746136 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 1, 5, 2]
def baseStart_746136 : Nat := 118140960795 + 746136 * 2 ^ 59
def prefixEnd_746136 : Nat := 4983230072969 + 3 ^ 40 * 746136 * 2
def baseEnd_746136 : Nat := 383126401623197973168589

theorem tailTrace_746136 : CollatzResearch.WordTrace tailWord_746136 prefixEnd_746136 383126401623197973168589 := by
  unfold tailWord_746136
  simp only [CollatzResearch.WordTrace]
  refine ⟨13606907812442088364349131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18142543749922784485798841 13606907812442088364349131)
  ·
    refine ⟨20410361718663132546523697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13606907812442088364349131 20410361718663132546523697)
    ·
      refine ⟨15307771288997349409892773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20410361718663132546523697 15307771288997349409892773)
      ·
        refine ⟨2870207116687003014354895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15307771288997349409892773 2870207116687003014354895)
        ·
          refine ⟨4305310675030504521532343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870207116687003014354895 4305310675030504521532343)
          ·
            refine ⟨6457966012545756782298515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305310675030504521532343 6457966012545756782298515)
            ·
              refine ⟨9686949018818635173447773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6457966012545756782298515 9686949018818635173447773)
              ·
                refine ⟨3632605882056988190042915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9686949018818635173447773 3632605882056988190042915)
                ·
                  refine ⟨5448908823085482285064373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632605882056988190042915 5448908823085482285064373)
                  ·
                    refine ⟨510835202164263964224785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5448908823085482285064373 510835202164263964224785)
                    ·
                      refine ⟨383126401623197973168589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510835202164263964224785 383126401623197973168589)
                      ·
                        rfl

theorem cell23_746136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_746136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746136 prefixEnd_746136 := by exact prefixLift 746136
  have htrace : WordTrace (prefixWord ++ tailWord_746136) baseStart_746136 baseEnd_746136 := by
    simpa [prefixWord, tailWord_746136, baseEnd_746136] using wordTrace_append hprefix tailTrace_746136
  have hstable : (prefixWord ++ tailWord_746136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746136).length < 2 ^ (prefixWord ++ tailWord_746136).sum := by decide
  have hdescent : baseEnd_746136 < baseStart_746136 := by decide
  rcases family_descends (prefixWord ++ tailWord_746136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746149 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_746149 : Nat := 118140960795 + 746149 * 2 ^ 59
def prefixEnd_746149 : Nat := 4983230072969 + 3 ^ 40 * 746149 * 2
def baseEnd_746149 : Nat := 383133076871706422306029

theorem tailTrace_746149 : CollatzResearch.WordTrace tailWord_746149 prefixEnd_746149 383133076871706422306029 := by
  unfold tailWord_746149
  simp only [CollatzResearch.WordTrace]
  refine ⟨27214289773837079948921501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18142859849224719965947667 27214289773837079948921501)
  ·
    refine ⟨10205358665188904980845563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27214289773837079948921501 10205358665188904980845563)
    ·
      refine ⟨15308037997783357471268345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10205358665188904980845563 15308037997783357471268345)
      ·
        refine ⟨11481028498337518103451259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15308037997783357471268345 11481028498337518103451259)
        ·
          refine ⟨17221542747506277155176889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11481028498337518103451259 17221542747506277155176889)
          ·
            refine ⟨12916157060629707866382667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17221542747506277155176889 12916157060629707866382667)
            ·
              refine ⟨19374235590944561799574001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12916157060629707866382667 19374235590944561799574001)
              ·
                refine ⟨14530676693208421349680501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19374235590944561799574001 14530676693208421349680501)
                ·
                  refine ⟨1362250939988289501532547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14530676693208421349680501 1362250939988289501532547)
                  ·
                    refine ⟨2043376409982434252298821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1362250939988289501532547 2043376409982434252298821)
                    ·
                      refine ⟨383133076871706422306029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2043376409982434252298821 383133076871706422306029)
                      ·
                        rfl

theorem cell23_746149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_746149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746149 prefixEnd_746149 := by exact prefixLift 746149
  have htrace : WordTrace (prefixWord ++ tailWord_746149) baseStart_746149 baseEnd_746149 := by
    simpa [prefixWord, tailWord_746149, baseEnd_746149] using wordTrace_append hprefix tailTrace_746149
  have hstable : (prefixWord ++ tailWord_746149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746149).length < 2 ^ (prefixWord ++ tailWord_746149).sum := by decide
  have hdescent : baseEnd_746149 < baseStart_746149 := by decide
  rcases family_descends (prefixWord ++ tailWord_746149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746154 : List Nat := [3, 1, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_746154 : Nat := 118140960795 + 746154 * 2 ^ 59
def prefixEnd_746154 : Nat := 4983230072969 + 3 ^ 40 * 746154 * 2
def baseEnd_746154 : Nat := 127711881424992967581169

theorem tailTrace_746154 : CollatzResearch.WordTrace tailWord_746154 prefixEnd_746154 127711881424992967581169 := by
  unfold tailWord_746154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6803618034704741450713379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18142981425879310535235677 6803618034704741450713379)
  ·
    refine ⟨10205427052057112176070069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6803618034704741450713379 10205427052057112176070069)
    ·
      refine ⟨956758786130354266506569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10205427052057112176070069 956758786130354266506569)
      ·
        refine ⟨717569089597765699879927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 956758786130354266506569 717569089597765699879927)
        ·
          refine ⟨1076353634396648549819891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717569089597765699879927 1076353634396648549819891)
          ·
            refine ⟨1614530451594972824729837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076353634396648549819891 1614530451594972824729837)
            ·
              refine ⟨605448919348114809273689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1614530451594972824729837 605448919348114809273689)
              ·
                refine ⟨454086689511086106955267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605448919348114809273689 454086689511086106955267)
                ·
                  refine ⟨681130034266629160432901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454086689511086106955267 681130034266629160432901)
                  ·
                    refine ⟨127711881424992967581169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681130034266629160432901 127711881424992967581169)
                    ·
                      rfl

theorem cell23_746154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_746154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746154 prefixEnd_746154 := by exact prefixLift 746154
  have htrace : WordTrace (prefixWord ++ tailWord_746154) baseStart_746154 baseEnd_746154 := by
    simpa [prefixWord, tailWord_746154, baseEnd_746154] using wordTrace_append hprefix tailTrace_746154
  have hstable : (prefixWord ++ tailWord_746154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746154).length < 2 ^ (prefixWord ++ tailWord_746154).sum := by decide
  have hdescent : baseEnd_746154 < baseStart_746154 := by decide
  rcases family_descends (prefixWord ++ tailWord_746154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746169 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 3]
def baseStart_746169 : Nat := 118140960795 + 746169 * 2 ^ 59
def prefixEnd_746169 : Nat := 4983230072969 + 3 ^ 40 * 746169 * 2
def baseEnd_746169 : Nat := 383143346484796344055937

theorem tailTrace_746169 : CollatzResearch.WordTrace tailWord_746169 prefixEnd_746169 383143346484796344055937 := by
  unfold tailWord_746169
  simp only [CollatzResearch.WordTrace]
  refine ⟨27215019233764623364649561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18143346155843082243099707 27215019233764623364649561)
  ·
    refine ⟨20411264425323467523487171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27215019233764623364649561 20411264425323467523487171)
    ·
      refine ⟨30616896637985201285230757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20411264425323467523487171 30616896637985201285230757)
      ·
        refine ⟨5740668119622225240980767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30616896637985201285230757 5740668119622225240980767)
        ·
          refine ⟨8611002179433337861471151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5740668119622225240980767 8611002179433337861471151)
          ·
            refine ⟨12916503269150006792206727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8611002179433337861471151 12916503269150006792206727)
            ·
              refine ⟨19374754903725010188310091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12916503269150006792206727 19374754903725010188310091)
              ·
                refine ⟨29062132355587515282465137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19374754903725010188310091 29062132355587515282465137)
                ·
                  refine ⟨21796599266690636461848853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29062132355587515282465137 21796599266690636461848853)
                  ·
                    refine ⟨1021715590626123584149165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21796599266690636461848853 1021715590626123584149165)
                    ·
                      refine ⟨383143346484796344055937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1021715590626123584149165 383143346484796344055937)
                      ·
                        rfl

theorem cell23_746169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_746169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746169 prefixEnd_746169 := by exact prefixLift 746169
  have htrace : WordTrace (prefixWord ++ tailWord_746169) baseStart_746169 baseEnd_746169 := by
    simpa [prefixWord, tailWord_746169, baseEnd_746169] using wordTrace_append hprefix tailTrace_746169
  have hstable : (prefixWord ++ tailWord_746169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746169).length < 2 ^ (prefixWord ++ tailWord_746169).sum := by decide
  have hdescent : baseEnd_746169 < baseStart_746169 := by decide
  rcases family_descends (prefixWord ++ tailWord_746169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746217 : List Nat := [1, 2, 1, 1, 1, 2, 8, 2, 1, 2, 2]
def baseStart_746217 : Nat := 118140960795 + 746217 * 2 ^ 59
def prefixEnd_746217 : Nat := 4983230072969 + 3 ^ 40 * 746217 * 2
def baseEnd_746217 : Nat := 383167993556212156255717

theorem tailTrace_746217 : CollatzResearch.WordTrace tailWord_746217 prefixEnd_746217 383167993556212156255717 := by
  unfold tailWord_746217
  simp only [CollatzResearch.WordTrace]
  refine ⟨27216769937590727562396905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18144513291727151708264603 27216769937590727562396905)
  ·
    refine ⟨20412577453193045671797679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27216769937590727562396905 20412577453193045671797679)
    ·
      refine ⟨30618866179789568507696519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20412577453193045671797679 30618866179789568507696519)
      ·
        refine ⟨45928299269684352761544779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30618866179789568507696519 45928299269684352761544779)
        ·
          refine ⟨68892448904526529142317169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45928299269684352761544779 68892448904526529142317169)
          ·
            refine ⟨51669336678394896856737877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68892448904526529142317169 51669336678394896856737877)
            ·
              refine ⟨605500039199940197539897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 51669336678394896856737877 605500039199940197539897)
              ·
                refine ⟨454125029399955148154923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605500039199940197539897 454125029399955148154923)
                ·
                  refine ⟨681187544099932722232385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454125029399955148154923 681187544099932722232385)
                  ·
                    refine ⟨510890658074949541674289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 681187544099932722232385 510890658074949541674289)
                    ·
                      refine ⟨383167993556212156255717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510890658074949541674289 383167993556212156255717)
                      ·
                        rfl

theorem cell23_746217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 2, 1, 2, 2].length) (baseStart_746217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746217 prefixEnd_746217 := by exact prefixLift 746217
  have htrace : WordTrace (prefixWord ++ tailWord_746217) baseStart_746217 baseEnd_746217 := by
    simpa [prefixWord, tailWord_746217, baseEnd_746217] using wordTrace_append hprefix tailTrace_746217
  have hstable : (prefixWord ++ tailWord_746217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746217).length < 2 ^ (prefixWord ++ tailWord_746217).sum := by decide
  have hdescent : baseEnd_746217 < baseStart_746217 := by decide
  rcases family_descends (prefixWord ++ tailWord_746217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746239 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 4]
def baseStart_746239 : Nat := 118140960795 + 746239 * 2 ^ 59
def prefixEnd_746239 : Nat := 4983230072969 + 3 ^ 40 * 746239 * 2
def baseEnd_746239 : Nat := 383179290130611070180615

theorem tailTrace_746239 : CollatzResearch.WordTrace tailWord_746239 prefixEnd_746239 383179290130611070180615 := by
  unfold tailWord_746239
  simp only [CollatzResearch.WordTrace]
  refine ⟨27217572343511025319697771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18145048229007350213131847 27217572343511025319697771)
  ·
    refine ⟨40826358515266537979546657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27217572343511025319697771 40826358515266537979546657)
    ·
      refine ⟨30619768886449903484659993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40826358515266537979546657 30619768886449903484659993)
      ·
        refine ⟨22964826664837427613494995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30619768886449903484659993 22964826664837427613494995)
        ·
          refine ⟨34447239997256141420242493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22964826664837427613494995 34447239997256141420242493)
          ·
            refine ⟨12917714998971053032590935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34447239997256141420242493 12917714998971053032590935)
            ·
              refine ⟨19376572498456579548886403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12917714998971053032590935 19376572498456579548886403)
              ·
                refine ⟨29064858747684869323329605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19376572498456579548886403 29064858747684869323329605)
                ·
                  refine ⟨5449661015190912998124301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29064858747684869323329605 5449661015190912998124301)
                  ·
                    refine ⟨2043622880696592374296613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5449661015190912998124301 2043622880696592374296613)
                    ·
                      refine ⟨383179290130611070180615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2043622880696592374296613 383179290130611070180615)
                      ·
                        rfl

theorem cell23_746239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_746239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746239 prefixEnd_746239 := by exact prefixLift 746239
  have htrace : WordTrace (prefixWord ++ tailWord_746239) baseStart_746239 baseEnd_746239 := by
    simpa [prefixWord, tailWord_746239, baseEnd_746239] using wordTrace_append hprefix tailTrace_746239
  have hstable : (prefixWord ++ tailWord_746239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746239).length < 2 ^ (prefixWord ++ tailWord_746239).sum := by decide
  have hdescent : baseEnd_746239 < baseStart_746239 := by decide
  rcases family_descends (prefixWord ++ tailWord_746239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746243 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 1, 3, 2]
def baseStart_746243 : Nat := 118140960795 + 746243 * 2 ^ 59
def prefixEnd_746243 : Nat := 4983230072969 + 3 ^ 40 * 746243 * 2
def baseEnd_746243 : Nat := 383181344053229054530597

theorem tailTrace_746243 : CollatzResearch.WordTrace tailWord_746243 prefixEnd_746243 383181344053229054530597 := by
  unfold tailWord_746243
  simp only [CollatzResearch.WordTrace]
  refine ⟨27217718235496534002843383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18145145490331022668562255 27217718235496534002843383)
  ·
    refine ⟨40826577353244801004265075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27217718235496534002843383 40826577353244801004265075)
    ·
      refine ⟨61239866029867201506397613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40826577353244801004265075 61239866029867201506397613)
      ·
        refine ⟨22964949761200200564899105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61239866029867201506397613 22964949761200200564899105)
        ·
          refine ⟨17223712320900150423674329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22964949761200200564899105 17223712320900150423674329)
          ·
            refine ⟨12917784240675112817755747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17223712320900150423674329 12917784240675112817755747)
            ·
              refine ⟨19376676361012669226633621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12917784240675112817755747 19376676361012669226633621)
              ·
                refine ⟨908281704422468869998451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19376676361012669226633621 908281704422468869998451)
                ·
                  refine ⟨1362422556633703304997677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908281704422468869998451 1362422556633703304997677)
                  ·
                    refine ⟨510908458737638739374129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362422556633703304997677 510908458737638739374129)
                    ·
                      refine ⟨383181344053229054530597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510908458737638739374129 383181344053229054530597)
                      ·
                        rfl

theorem cell23_746243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_746243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746243 prefixEnd_746243 := by exact prefixLift 746243
  have htrace : WordTrace (prefixWord ++ tailWord_746243) baseStart_746243 baseEnd_746243 := by
    simpa [prefixWord, tailWord_746243, baseEnd_746243] using wordTrace_append hprefix tailTrace_746243
  have hstable : (prefixWord ++ tailWord_746243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746243).length < 2 ^ (prefixWord ++ tailWord_746243).sum := by decide
  have hdescent : baseEnd_746243 < baseStart_746243 := by decide
  rcases family_descends (prefixWord ++ tailWord_746243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746259 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 5]
def baseStart_746259 : Nat := 118140960795 + 746259 * 2 ^ 59
def prefixEnd_746259 : Nat := 4983230072969 + 3 ^ 40 * 746259 * 2
def baseEnd_746259 : Nat := 383189559743700991930523

theorem tailTrace_746259 : CollatzResearch.WordTrace tailWord_746259 prefixEnd_746259 383189559743700991930523 := by
  unfold tailWord_746259
  simp only [CollatzResearch.WordTrace]
  refine ⟨27218301803438568735425831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18145534535625712490283887 27218301803438568735425831)
  ·
    refine ⟨40827452705157853103138747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27218301803438568735425831 40827452705157853103138747)
    ·
      refine ⟨61241179057736779654708121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40827452705157853103138747 61241179057736779654708121)
      ·
        refine ⟨45930884293302584741031091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61241179057736779654708121 45930884293302584741031091)
        ·
          refine ⟨68896326439953877111546637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45930884293302584741031091 68896326439953877111546637)
          ·
            refine ⟨25836122414982703916829989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68896326439953877111546637 25836122414982703916829989)
            ·
              refine ⟨4844272952809256984405623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25836122414982703916829989 4844272952809256984405623)
              ·
                refine ⟨7266409429213885476608435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4844272952809256984405623 7266409429213885476608435)
                ·
                  refine ⟨10899614143820828214912653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7266409429213885476608435 10899614143820828214912653)
                  ·
                    refine ⟨4087355303932810580592245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10899614143820828214912653 4087355303932810580592245)
                    ·
                      refine ⟨383189559743700991930523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4087355303932810580592245 383189559743700991930523)
                      ·
                        rfl

theorem cell23_746259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_746259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746259 prefixEnd_746259 := by exact prefixLift 746259
  have htrace : WordTrace (prefixWord ++ tailWord_746259) baseStart_746259 baseEnd_746259 := by
    simpa [prefixWord, tailWord_746259, baseEnd_746259] using wordTrace_append hprefix tailTrace_746259
  have hstable : (prefixWord ++ tailWord_746259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746259).length < 2 ^ (prefixWord ++ tailWord_746259).sum := by decide
  have hdescent : baseEnd_746259 < baseStart_746259 := by decide
  rcases family_descends (prefixWord ++ tailWord_746259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746294 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_746294 : Nat := 118140960795 + 746294 * 2 ^ 59
def prefixEnd_746294 : Nat := 4983230072969 + 3 ^ 40 * 746294 * 2
def baseEnd_746294 : Nat := 383207531566608354992863

theorem tailTrace_746294 : CollatzResearch.WordTrace tailWord_746294 prefixEnd_746294 383207531566608354992863 := by
  unfold tailWord_746294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701223647394485607059371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18146385572207846475299957 1701223647394485607059371)
  ·
    refine ⟨2551835471091728410589057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701223647394485607059371 2551835471091728410589057)
    ·
      refine ⟨1913876603318796307941793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2551835471091728410589057 1913876603318796307941793)
      ·
        refine ⟨1435407452489097230956345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1913876603318796307941793 1435407452489097230956345)
        ·
          refine ⟨1076555589366822923217259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1435407452489097230956345 1076555589366822923217259)
          ·
            refine ⟨1614833384050234384825889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076555589366822923217259 1614833384050234384825889)
            ·
              refine ⟨1211125038037675788619417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1614833384050234384825889 1211125038037675788619417)
              ·
                refine ⟨908343778528256841464563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211125038037675788619417 908343778528256841464563)
                ·
                  refine ⟨1362515667792385262196845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908343778528256841464563 1362515667792385262196845)
                  ·
                    refine ⟨510943375422144473323817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1362515667792385262196845 510943375422144473323817)
                    ·
                      refine ⟨383207531566608354992863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 510943375422144473323817 383207531566608354992863)
                      ·
                        rfl

theorem cell23_746294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_746294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746294 prefixEnd_746294 := by exact prefixLift 746294
  have htrace : WordTrace (prefixWord ++ tailWord_746294) baseStart_746294 baseEnd_746294 := by
    simpa [prefixWord, tailWord_746294, baseEnd_746294] using wordTrace_append hprefix tailTrace_746294
  have hstable : (prefixWord ++ tailWord_746294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746294).length < 2 ^ (prefixWord ++ tailWord_746294).sum := by decide
  have hdescent : baseEnd_746294 < baseStart_746294 := by decide
  rcases family_descends (prefixWord ++ tailWord_746294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746313 : List Nat := [1, 2, 1, 1, 2, 5, 3, 3, 5]
def baseStart_746313 : Nat := 118140960795 + 746313 * 2 ^ 59
def prefixEnd_746313 : Nat := 4983230072969 + 3 ^ 40 * 746313 * 2
def baseEnd_746313 : Nat := 42579698633227086739475

theorem tailTrace_746313 : CollatzResearch.WordTrace tailWord_746313 prefixEnd_746313 42579698633227086739475 := by
  unfold tailWord_746313
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220271345242935957891593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18146847563495290638594395 27220271345242935957891593)
  ·
    refine ⟨20415203508932201968418695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27220271345242935957891593 20415203508932201968418695)
    ·
      refine ⟨30622805263398302952628043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20415203508932201968418695 30622805263398302952628043)
      ·
        refine ⟨45934207895097454428942065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30622805263398302952628043 45934207895097454428942065)
        ·
          refine ⟨34450655921323090821706549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45934207895097454428942065 34450655921323090821706549)
          ·
            refine ⟨3229748992624039764534989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34450655921323090821706549 3229748992624039764534989)
            ·
              refine ⟨1211155872234014911700621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3229748992624039764534989 1211155872234014911700621)
              ·
                refine ⟨454183452087755591887733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1211155872234014911700621 454183452087755591887733)
                ·
                  refine ⟨42579698633227086739475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 454183452087755591887733 42579698633227086739475)
                  ·
                    rfl

theorem cell23_746313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 5].length) (baseStart_746313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746313 prefixEnd_746313 := by exact prefixLift 746313
  have htrace : WordTrace (prefixWord ++ tailWord_746313) baseStart_746313 baseEnd_746313 := by
    simpa [prefixWord, tailWord_746313, baseEnd_746313] using wordTrace_append hprefix tailTrace_746313
  have hstable : (prefixWord ++ tailWord_746313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746313).length < 2 ^ (prefixWord ++ tailWord_746313).sum := by decide
  have hdescent : baseEnd_746313 < baseStart_746313 := by decide
  rcases family_descends (prefixWord ++ tailWord_746313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746319 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_746319 : Nat := 118140960795 + 746319 * 2 ^ 59
def prefixEnd_746319 : Nat := 4983230072969 + 3 ^ 40 * 746319 * 2
def baseEnd_746319 : Nat := 383220368582970757180247

theorem tailTrace_746319 : CollatzResearch.WordTrace tailWord_746319 prefixEnd_746319 383220368582970757180247 := by
  unfold tailWord_746319
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220490183221198982610011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18146993455480799321740007 27220490183221198982610011)
  ·
    refine ⟨40830735274831798473915017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27220490183221198982610011 40830735274831798473915017)
    ·
      refine ⟨30623051456123848855436263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40830735274831798473915017 30623051456123848855436263)
      ·
        refine ⟨45934577184185773283154395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30623051456123848855436263 45934577184185773283154395)
        ·
          refine ⟨68901865776278659924731593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45934577184185773283154395 68901865776278659924731593)
          ·
            refine ⟨51676399332208994943548695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68901865776278659924731593 51676399332208994943548695)
            ·
              refine ⟨77514598998313492415323043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51676399332208994943548695 77514598998313492415323043)
              ·
                refine ⟨116271898497470238622984565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77514598998313492415323043 116271898497470238622984565)
                ·
                  refine ⟨10900490484137834870904803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116271898497470238622984565 10900490484137834870904803)
                  ·
                    refine ⟨16350735726206752306357205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10900490484137834870904803 16350735726206752306357205)
                    ·
                      refine ⟨383220368582970757180247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16350735726206752306357205 383220368582970757180247)
                      ·
                        rfl

theorem cell23_746319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_746319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_746319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_746319 prefixEnd_746319 := by exact prefixLift 746319
  have htrace : WordTrace (prefixWord ++ tailWord_746319) baseStart_746319 baseEnd_746319 := by
    simpa [prefixWord, tailWord_746319, baseEnd_746319] using wordTrace_append hprefix tailTrace_746319
  have hstable : (prefixWord ++ tailWord_746319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746319).length < 2 ^ (prefixWord ++ tailWord_746319).sum := by decide
  have hdescent : baseEnd_746319 < baseStart_746319 := by decide
  rcases family_descends (prefixWord ++ tailWord_746319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
