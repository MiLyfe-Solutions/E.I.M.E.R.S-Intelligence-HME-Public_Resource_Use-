import V185TrunkScan22Chunk073

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_664807 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 2, 4]
def baseStart_664807 : Nat := 118140960795 + 664807 * 2 ^ 59
def prefixEnd_664807 : Nat := 4983230072969 + 3 ^ 40 * 664807 * 2
def baseEnd_664807 : Nat := 227577022315790448836743

theorem tailTrace_664807 : CollatzResearch.WordTrace tailWord_664807 prefixEnd_664807 227577022315790448836743 := by
  unfold tailWord_664807
  simp only [CollatzResearch.WordTrace]
  refine ⟨24247503302525253841328675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16165002201683502560885783 24247503302525253841328675)
  ·
    refine ⟨36371254953787880761993013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24247503302525253841328675 36371254953787880761993013)
    ·
      refine ⟨3409805151917613821436845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36371254953787880761993013 3409805151917613821436845)
      ·
        refine ⟨1278676931969105183038817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3409805151917613821436845 1278676931969105183038817)
        ·
          refine ⟨959007698976828887279113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1278676931969105183038817 959007698976828887279113)
          ·
            refine ⟨719255774232621665459335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959007698976828887279113 719255774232621665459335)
            ·
              refine ⟨1078883661348932498189003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719255774232621665459335 1078883661348932498189003)
              ·
                refine ⟨1618325492023398747283505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078883661348932498189003 1618325492023398747283505)
                ·
                  refine ⟨1213744119017549060462629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618325492023398747283505 1213744119017549060462629)
                  ·
                    refine ⟨227577022315790448836743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1213744119017549060462629 227577022315790448836743)
                    ·
                      rfl

theorem cell22_664807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_664807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664807 prefixEnd_664807 := by exact prefixLift 664807
  have htrace : WordTrace (prefixWord ++ tailWord_664807) baseStart_664807 baseEnd_664807 := by
    simpa [prefixWord, tailWord_664807, baseEnd_664807] using wordTrace_append hprefix tailTrace_664807
  have hstable : (prefixWord ++ tailWord_664807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664807).length < 2 ^ (prefixWord ++ tailWord_664807).sum := by decide
  have hdescent : baseEnd_664807 < baseStart_664807 := by decide
  rcases family_descends (prefixWord ++ tailWord_664807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664833 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 7]
def baseStart_664833 : Nat := 118140960795 + 664833 * 2 ^ 59
def prefixEnd_664833 : Nat := 4983230072969 + 3 ^ 40 * 664833 * 2
def baseEnd_664833 : Nat := 75861974215711682562221

theorem tailTrace_664833 : CollatzResearch.WordTrace tailWord_664833 prefixEnd_664833 75861974215711682562221 := by
  unfold tailWord_664833
  simp only [CollatzResearch.WordTrace]
  refine ⟨24248451600431060281775153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16165634400287373521183435 24248451600431060281775153)
  ·
    refine ⟨18186338700323295211331365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24248451600431060281775153 18186338700323295211331365)
    ·
      refine ⟨3409938506310617852124631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18186338700323295211331365 3409938506310617852124631)
      ·
        refine ⟨5114907759465926778186947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3409938506310617852124631 5114907759465926778186947)
        ·
          refine ⟨7672361639198890167280421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5114907759465926778186947 7672361639198890167280421)
          ·
            refine ⟨1438567807349791906365079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7672361639198890167280421 1438567807349791906365079)
            ·
              refine ⟨2157851711024687859547619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438567807349791906365079 2157851711024687859547619)
              ·
                refine ⟨3236777566537031789321429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157851711024687859547619 3236777566537031789321429)
                ·
                  refine ⟨75861974215711682562221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3236777566537031789321429 75861974215711682562221)
                  ·
                    rfl

theorem cell22_664833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_664833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664833 prefixEnd_664833 := by exact prefixLift 664833
  have htrace : WordTrace (prefixWord ++ tailWord_664833) baseStart_664833 baseEnd_664833 := by
    simpa [prefixWord, tailWord_664833, baseEnd_664833] using wordTrace_append hprefix tailTrace_664833
  have hstable : (prefixWord ++ tailWord_664833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664833).length < 2 ^ (prefixWord ++ tailWord_664833).sum := by decide
  have hdescent : baseEnd_664833 < baseStart_664833 := by decide
  rcases family_descends (prefixWord ++ tailWord_664833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664895 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 6]
def baseStart_664895 : Nat := 118140960795 + 664895 * 2 ^ 59
def prefixEnd_664895 : Nat := 4983230072969 + 3 ^ 40 * 664895 * 2
def baseEnd_664895 : Nat := 75869048838062517545491

theorem tailTrace_664895 : CollatzResearch.WordTrace tailWord_664895 prefixEnd_664895 75869048838062517545491 := by
  unfold tailWord_664895
  simp only [CollatzResearch.WordTrace]
  refine ⟨24250712926206444870532139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16167141950804296580354759 24250712926206444870532139)
  ·
    refine ⟨36376069389309667305798209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24250712926206444870532139 36376069389309667305798209)
    ·
      refine ⟨27282052041982250479348657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36376069389309667305798209 27282052041982250479348657)
      ·
        refine ⟨20461539031486687859511493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27282052041982250479348657 20461539031486687859511493)
        ·
          refine ⟨3836538568403753973658405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20461539031486687859511493 3836538568403753973658405)
          ·
            refine ⟨719350981575703870060951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3836538568403753973658405 719350981575703870060951)
            ·
              refine ⟨1079026472363555805091427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719350981575703870060951 1079026472363555805091427)
              ·
                refine ⟨1618539708545333707637141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079026472363555805091427 1618539708545333707637141)
                ·
                  refine ⟨75869048838062517545491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1618539708545333707637141 75869048838062517545491)
                  ·
                    rfl

theorem cell22_664895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 6].length) (baseStart_664895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664895 prefixEnd_664895 := by exact prefixLift 664895
  have htrace : WordTrace (prefixWord ++ tailWord_664895) baseStart_664895 baseEnd_664895 := by
    simpa [prefixWord, tailWord_664895, baseEnd_664895] using wordTrace_append hprefix tailTrace_664895
  have hstable : (prefixWord ++ tailWord_664895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664895).length < 2 ^ (prefixWord ++ tailWord_664895).sum := by decide
  have hdescent : baseEnd_664895 < baseStart_664895 := by decide
  rcases family_descends (prefixWord ++ tailWord_664895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664953 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_664953 : Nat := 118140960795 + 664953 * 2 ^ 59
def prefixEnd_664953 : Nat := 4983230072969 + 3 ^ 40 * 664953 * 2
def baseEnd_664953 : Nat := 227627001099494734686295

theorem tailTrace_664953 : CollatzResearch.WordTrace tailWord_664953 prefixEnd_664953 227627001099494734686295 := by
  unfold tailWord_664953
  simp only [CollatzResearch.WordTrace]
  refine ⟨24252828359996320776143513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16168552239997547184095675 24252828359996320776143513)
  ·
    refine ⟨18189621269997240582107635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24252828359996320776143513 18189621269997240582107635)
    ·
      refine ⟨27284431904995860873161453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18189621269997240582107635 27284431904995860873161453)
      ·
        refine ⟨10231661964373447827435545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27284431904995860873161453 10231661964373447827435545)
        ·
          refine ⟨7673746473280085870576659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10231661964373447827435545 7673746473280085870576659)
          ·
            refine ⟨11510619709920128805864989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7673746473280085870576659 11510619709920128805864989)
            ·
              refine ⟨4316482391220048302199371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11510619709920128805864989 4316482391220048302199371)
              ·
                refine ⟨6474723586830072453299057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4316482391220048302199371 6474723586830072453299057)
                ·
                  refine ⟨4856042690122554339974293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6474723586830072453299057 4856042690122554339974293)
                  ·
                    refine ⟨227627001099494734686295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4856042690122554339974293 227627001099494734686295)
                    ·
                      rfl

theorem cell22_664953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_664953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664953 prefixEnd_664953 := by exact prefixLift 664953
  have htrace : WordTrace (prefixWord ++ tailWord_664953) baseStart_664953 baseEnd_664953 := by
    simpa [prefixWord, tailWord_664953, baseEnd_664953] using wordTrace_append hprefix tailTrace_664953
  have hstable : (prefixWord ++ tailWord_664953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664953).length < 2 ^ (prefixWord ++ tailWord_664953).sum := by decide
  have hdescent : baseEnd_664953 < baseStart_664953 := by decide
  rcases family_descends (prefixWord ++ tailWord_664953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664955 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 3, 3]
def baseStart_664955 : Nat := 118140960795 + 664955 * 2 ^ 59
def prefixEnd_664955 : Nat := 4983230072969 + 3 ^ 40 * 664955 * 2
def baseEnd_664955 : Nat := 227627685740367396136289

theorem tailTrace_664955 : CollatzResearch.WordTrace tailWord_664955 prefixEnd_664955 227627685740367396136289 := by
  unfold tailWord_664955
  simp only [CollatzResearch.WordTrace]
  refine ⟨24252901305989075117716319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16168600870659383411810879 24252901305989075117716319)
  ·
    refine ⟨36379351958983612676574479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24252901305989075117716319 36379351958983612676574479)
    ·
      refine ⟨54569027938475419014861719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36379351958983612676574479 54569027938475419014861719)
      ·
        refine ⟨81853541907713128522292579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54569027938475419014861719 81853541907713128522292579)
        ·
          refine ⟨122780312861569692783438869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81853541907713128522292579 122780312861569692783438869)
          ·
            refine ⟨5755327165386079349223697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122780312861569692783438869 5755327165386079349223697)
            ·
              refine ⟨4316495374039559511917773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755327165386079349223697 4316495374039559511917773)
              ·
                refine ⟨1618685765264834816969165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4316495374039559511917773 1618685765264834816969165)
                ·
                  refine ⟨607007161974313056363437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1618685765264834816969165 607007161974313056363437)
                  ·
                    refine ⟨227627685740367396136289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607007161974313056363437 227627685740367396136289)
                    ·
                      rfl

theorem cell22_664955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 3].length) (baseStart_664955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664955 prefixEnd_664955 := by exact prefixLift 664955
  have htrace : WordTrace (prefixWord ++ tailWord_664955) baseStart_664955 baseEnd_664955 := by
    simpa [prefixWord, tailWord_664955, baseEnd_664955] using wordTrace_append hprefix tailTrace_664955
  have hstable : (prefixWord ++ tailWord_664955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664955).length < 2 ^ (prefixWord ++ tailWord_664955).sum := by decide
  have hdescent : baseEnd_664955 < baseStart_664955 := by decide
  rcases family_descends (prefixWord ++ tailWord_664955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664983 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 3, 7]
def baseStart_664983 : Nat := 118140960795 + 664983 * 2 ^ 59
def prefixEnd_664983 : Nat := 4983230072969 + 3 ^ 40 * 664983 * 2
def baseEnd_664983 : Nat := 227637270712584656436203

theorem tailTrace_664983 : CollatzResearch.WordTrace tailWord_664983 prefixEnd_664983 227637270712584656436203 := by
  unfold tailWord_664983
  simp only [CollatzResearch.WordTrace]
  refine ⟨24253922549887635899735603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16169281699925090599823735 24253922549887635899735603)
  ·
    refine ⟨36380883824831453849603405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24253922549887635899735603 36380883824831453849603405)
    ·
      refine ⟨13642831434311795193601277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36380883824831453849603405 13642831434311795193601277)
      ·
        refine ⟨5116061787866923197600479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13642831434311795193601277 5116061787866923197600479)
        ·
          refine ⟨7674092681800384796400719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116061787866923197600479 7674092681800384796400719)
          ·
            refine ⟨11511139022700577194601079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7674092681800384796400719 11511139022700577194601079)
            ·
              refine ⟨17266708534050865791901619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11511139022700577194601079 17266708534050865791901619)
              ·
                refine ⟨25900062801076298687852429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17266708534050865791901619 25900062801076298687852429)
                ·
                  refine ⟨9712523550403612007944661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25900062801076298687852429 9712523550403612007944661)
                  ·
                    refine ⟨227637270712584656436203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9712523550403612007944661 227637270712584656436203)
                    ·
                      rfl

theorem cell22_664983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_664983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664983 prefixEnd_664983 := by exact prefixLift 664983
  have htrace : WordTrace (prefixWord ++ tailWord_664983) baseStart_664983 baseEnd_664983 := by
    simpa [prefixWord, tailWord_664983, baseEnd_664983] using wordTrace_append hprefix tailTrace_664983
  have hstable : (prefixWord ++ tailWord_664983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664983).length < 2 ^ (prefixWord ++ tailWord_664983).sum := by decide
  have hdescent : baseEnd_664983 < baseStart_664983 := by decide
  rcases family_descends (prefixWord ++ tailWord_664983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664989 : List Nat := [1, 4, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_664989 : Nat := 118140960795 + 664989 * 2 ^ 59
def prefixEnd_664989 : Nat := 4983230072969 + 3 ^ 40 * 664989 * 2
def baseEnd_664989 : Nat := 227639324635202640786185

theorem tailTrace_664989 : CollatzResearch.WordTrace tailWord_664989 prefixEnd_664989 227639324635202640786185 := by
  unfold tailWord_664989
  simp only [CollatzResearch.WordTrace]
  refine ⟨24254141387865898924454021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16169427591910599282969347 24254141387865898924454021)
  ·
    refine ⟨4547651510224856048335129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24254141387865898924454021 4547651510224856048335129)
    ·
      refine ⟨3410738632668642036251347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4547651510224856048335129 3410738632668642036251347)
      ·
        refine ⟨5116107949002963054377021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410738632668642036251347 5116107949002963054377021)
        ·
          refine ⟨1918540480876111145391383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5116107949002963054377021 1918540480876111145391383)
          ·
            refine ⟨2877810721314166718087075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918540480876111145391383 2877810721314166718087075)
            ·
              refine ⟨4316716081971250077130613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877810721314166718087075 4316716081971250077130613)
              ·
                refine ⟨404692132684804694730995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4316716081971250077130613 404692132684804694730995)
                ·
                  refine ⟨607038199027207042096493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404692132684804694730995 607038199027207042096493)
                  ·
                    refine ⟨227639324635202640786185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607038199027207042096493 227639324635202640786185)
                    ·
                      rfl

theorem cell22_664989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_664989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_664989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_664989 prefixEnd_664989 := by exact prefixLift 664989
  have htrace : WordTrace (prefixWord ++ tailWord_664989) baseStart_664989 baseEnd_664989 := by
    simpa [prefixWord, tailWord_664989, baseEnd_664989] using wordTrace_append hprefix tailTrace_664989
  have hstable : (prefixWord ++ tailWord_664989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664989).length < 2 ^ (prefixWord ++ tailWord_664989).sum := by decide
  have hdescent : baseEnd_664989 < baseStart_664989 := by decide
  rcases family_descends (prefixWord ++ tailWord_664989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665032 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_665032 : Nat := 118140960795 + 665032 * 2 ^ 59
def prefixEnd_665032 : Nat := 4983230072969 + 3 ^ 40 * 665032 * 2
def baseEnd_665032 : Nat := 227654044413964861961053

theorem tailTrace_665032 : CollatzResearch.WordTrace tailWord_665032 prefixEnd_665032 227654044413964861961053 := by
  unfold tailWord_665032
  simp only [CollatzResearch.WordTrace]
  refine ⟨12127854863355058634134675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16170473151140078178846233 12127854863355058634134675)
  ·
    refine ⟨18191782295032587951202013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12127854863355058634134675 18191782295032587951202013)
    ·
      refine ⟨6821918360637220481700755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18191782295032587951202013 6821918360637220481700755)
      ·
        refine ⟨10232877540955830722551133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6821918360637220481700755 10232877540955830722551133)
        ·
          refine ⟨3837329077858436520956675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10232877540955830722551133 3837329077858436520956675)
          ·
            refine ⟨5755993616787654781435013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837329077858436520956675 5755993616787654781435013)
            ·
              refine ⟨1079248803147685271519065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5755993616787654781435013 1079248803147685271519065)
              ·
                refine ⟨809436602360763953639299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079248803147685271519065 809436602360763953639299)
                ·
                  refine ⟨1214154903541145930458949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809436602360763953639299 1214154903541145930458949)
                  ·
                    refine ⟨227654044413964861961053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1214154903541145930458949 227654044413964861961053)
                    ·
                      rfl

theorem cell22_665032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_665032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665032 prefixEnd_665032 := by exact prefixLift 665032
  have htrace : WordTrace (prefixWord ++ tailWord_665032) baseStart_665032 baseEnd_665032 := by
    simpa [prefixWord, tailWord_665032, baseEnd_665032] using wordTrace_append hprefix tailTrace_665032
  have hstable : (prefixWord ++ tailWord_665032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665032).length < 2 ^ (prefixWord ++ tailWord_665032).sum := by decide
  have hdescent : baseEnd_665032 < baseStart_665032 := by decide
  rcases family_descends (prefixWord ++ tailWord_665032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665045 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_665045 : Nat := 118140960795 + 665045 * 2 ^ 59
def prefixEnd_665045 : Nat := 4983230072969 + 3 ^ 40 * 665045 * 2
def baseEnd_665045 : Nat := 227658494579637161386013

theorem tailTrace_665045 : CollatzResearch.WordTrace tailWord_665045 prefixEnd_665045 227658494579637161386013 := by
  unfold tailWord_665045
  simp only [CollatzResearch.WordTrace]
  refine ⟨24256183875663020488492589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16170789250442013658995059 24256183875663020488492589)
  ·
    refine ⟨9096068953373632683184721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24256183875663020488492589 9096068953373632683184721)
    ·
      refine ⟨6822051715030224512388541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9096068953373632683184721 6822051715030224512388541)
      ·
        refine ⟨2558269393136334192145703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6822051715030224512388541 2558269393136334192145703)
        ·
          refine ⟨3837404089704501288218555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558269393136334192145703 3837404089704501288218555)
          ·
            refine ⟨5756106134556751932327833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837404089704501288218555 5756106134556751932327833)
            ·
              refine ⟨4317079600917563949245875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5756106134556751932327833 4317079600917563949245875)
              ·
                refine ⟨6475619401376345923868813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317079600917563949245875 6475619401376345923868813)
                ·
                  refine ⟨2428357275516129721450805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6475619401376345923868813 2428357275516129721450805)
                  ·
                    refine ⟨227658494579637161386013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2428357275516129721450805 227658494579637161386013)
                    ·
                      rfl

theorem cell22_665045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_665045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665045 prefixEnd_665045 := by exact prefixLift 665045
  have htrace : WordTrace (prefixWord ++ tailWord_665045) baseStart_665045 baseEnd_665045 := by
    simpa [prefixWord, tailWord_665045, baseEnd_665045] using wordTrace_append hprefix tailTrace_665045
  have hstable : (prefixWord ++ tailWord_665045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665045).length < 2 ^ (prefixWord ++ tailWord_665045).sum := by decide
  have hdescent : baseEnd_665045 < baseStart_665045 := by decide
  rcases family_descends (prefixWord ++ tailWord_665045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665064 : List Nat := [2, 1, 4, 1, 1, 2, 5, 2, 4]
def baseStart_665064 : Nat := 118140960795 + 665064 * 2 ^ 59
def prefixEnd_665064 : Nat := 4983230072969 + 3 ^ 40 * 665064 * 2
def baseEnd_665064 : Nat := 75888332889309148386985

theorem tailTrace_665064 : CollatzResearch.WordTrace tailWord_665064 prefixEnd_665064 75888332889309148386985 := by
  unfold tailWord_665064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128438431297093366717123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16171251241729457822289497 12128438431297093366717123)
  ·
    refine ⟨18192657646945640050075685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12128438431297093366717123 18192657646945640050075685)
    ·
      refine ⟨3411123308802307509389191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18192657646945640050075685 3411123308802307509389191)
      ·
        refine ⟨5116684963203461264083787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411123308802307509389191 5116684963203461264083787)
        ·
          refine ⟨7675027444805191896125681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116684963203461264083787 7675027444805191896125681)
          ·
            refine ⟨5756270583603893922094261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7675027444805191896125681 5756270583603893922094261)
            ·
              refine ⟨539650367212865055196337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5756270583603893922094261 539650367212865055196337)
              ·
                refine ⟨404737775409648791397253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539650367212865055196337 404737775409648791397253)
                ·
                  refine ⟨75888332889309148386985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404737775409648791397253 75888332889309148386985)
                  ·
                    rfl

theorem cell22_665064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 4].length) (baseStart_665064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665064 prefixEnd_665064 := by exact prefixLift 665064
  have htrace : WordTrace (prefixWord ++ tailWord_665064) baseStart_665064 baseEnd_665064 := by
    simpa [prefixWord, tailWord_665064, baseEnd_665064] using wordTrace_append hprefix tailTrace_665064
  have hstable : (prefixWord ++ tailWord_665064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665064).length < 2 ^ (prefixWord ++ tailWord_665064).sum := by decide
  have hdescent : baseEnd_665064 < baseStart_665064 := by decide
  rcases family_descends (prefixWord ++ tailWord_665064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665212 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_665212 : Nat := 118140960795 + 665212 * 2 ^ 59
def prefixEnd_665212 : Nat := 4983230072969 + 3 ^ 40 * 665212 * 2
def baseEnd_665212 : Nat := 227715662092504392460501

theorem tailTrace_665212 : CollatzResearch.WordTrace tailWord_665212 prefixEnd_665212 227715662092504392460501 := by
  unfold tailWord_665212
  simp only [CollatzResearch.WordTrace]
  refine ⟨12131137433029004004910945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16174849910705338673214593 12131137433029004004910945)
  ·
    refine ⟨9098353074771753003683209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12131137433029004004910945 9098353074771753003683209)
    ·
      refine ⟨6823764806078814752762407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9098353074771753003683209 6823764806078814752762407)
      ·
        refine ⟨10235647209118222129143611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6823764806078814752762407 10235647209118222129143611)
        ·
          refine ⟨15353470813677333193715417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10235647209118222129143611 15353470813677333193715417)
          ·
            refine ⟨11515103110257999895286563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15353470813677333193715417 11515103110257999895286563)
            ·
              refine ⟨17272654665386999842929845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11515103110257999895286563 17272654665386999842929845)
              ·
                refine ⟨1619311374880031235274673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17272654665386999842929845 1619311374880031235274673)
                ·
                  refine ⟨1214483531160023426456005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1619311374880031235274673 1214483531160023426456005)
                  ·
                    refine ⟨227715662092504392460501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1214483531160023426456005 227715662092504392460501)
                    ·
                      rfl

theorem cell22_665212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_665212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665212 prefixEnd_665212 := by exact prefixLift 665212
  have htrace : WordTrace (prefixWord ++ tailWord_665212) baseStart_665212 baseEnd_665212 := by
    simpa [prefixWord, tailWord_665212, baseEnd_665212] using wordTrace_append hprefix tailTrace_665212
  have hstable : (prefixWord ++ tailWord_665212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665212).length < 2 ^ (prefixWord ++ tailWord_665212).sum := by decide
  have hdescent : baseEnd_665212 < baseStart_665212 := by decide
  rcases family_descends (prefixWord ++ tailWord_665212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665244 : List Nat := [2, 2, 3, 2, 3, 1, 2, 7]
def baseStart_665244 : Nat := 118140960795 + 665244 * 2 ^ 59
def prefixEnd_665244 : Nat := 4983230072969 + 3 ^ 40 * 665244 * 2
def baseEnd_665244 : Nat := 25302957371829663962267

theorem tailTrace_665244 : CollatzResearch.WordTrace tailWord_665244 prefixEnd_665244 25302957371829663962267 := by
  unfold tailWord_665244
  simp only [CollatzResearch.WordTrace]
  refine ⟨12131721000971038737493393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16175628001294718316657857 12131721000971038737493393)
  ·
    refine ⟨9098790750728279053120045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12131721000971038737493393 9098790750728279053120045)
    ·
      refine ⟨3412046531523104644920017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9098790750728279053120045 3412046531523104644920017)
      ·
        refine ⟨2559034898642328483690013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3412046531523104644920017 2559034898642328483690013)
        ·
          refine ⟨959638086990873181383755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2559034898642328483690013 959638086990873181383755)
          ·
            refine ⟨1439457130486309772075633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959638086990873181383755 1439457130486309772075633)
            ·
              refine ⟨1079592847864732329056725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439457130486309772075633 1079592847864732329056725)
              ·
                refine ⟨25302957371829663962267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1079592847864732329056725 25302957371829663962267)
                ·
                  rfl

theorem cell22_665244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 7].length) (baseStart_665244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665244 prefixEnd_665244 := by exact prefixLift 665244
  have htrace : WordTrace (prefixWord ++ tailWord_665244) baseStart_665244 baseEnd_665244 := by
    simpa [prefixWord, tailWord_665244, baseEnd_665244] using wordTrace_append hprefix tailTrace_665244
  have hstable : (prefixWord ++ tailWord_665244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665244).length < 2 ^ (prefixWord ++ tailWord_665244).sum := by decide
  have hdescent : baseEnd_665244 < baseStart_665244 := by decide
  rcases family_descends (prefixWord ++ tailWord_665244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665248 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 2, 3]
def baseStart_665248 : Nat := 118140960795 + 665248 * 2 ^ 59
def prefixEnd_665248 : Nat := 4983230072969 + 3 ^ 40 * 665248 * 2
def baseEnd_665248 : Nat := 227727985628212298560391

theorem tailTrace_665248 : CollatzResearch.WordTrace tailWord_665248 prefixEnd_665248 227727985628212298560391 := by
  unfold tailWord_665248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12131793946963793079066199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16175725262618390772088265 12131793946963793079066199)
  ·
    refine ⟨18197690920445689618599299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12131793946963793079066199 18197690920445689618599299)
    ·
      refine ⟨27296536380668534427898949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18197690920445689618599299 27296536380668534427898949)
      ·
        refine ⟨5118100571375350205231053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27296536380668534427898949 5118100571375350205231053)
        ·
          refine ⟨1919287714265756326961645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5118100571375350205231053 1919287714265756326961645)
          ·
            refine ⟨719732892849658622610617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1919287714265756326961645 719732892849658622610617)
            ·
              refine ⟨539799669637243966957963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719732892849658622610617 539799669637243966957963)
              ·
                refine ⟨809699504455865950436945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539799669637243966957963 809699504455865950436945)
                ·
                  refine ⟨607274628341899462827709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809699504455865950436945 607274628341899462827709)
                  ·
                    refine ⟨227727985628212298560391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607274628341899462827709 227727985628212298560391)
                    ·
                      rfl

theorem cell22_665248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 3].length) (baseStart_665248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665248 prefixEnd_665248 := by exact prefixLift 665248
  have htrace : WordTrace (prefixWord ++ tailWord_665248) baseStart_665248 baseEnd_665248 := by
    simpa [prefixWord, tailWord_665248, baseEnd_665248] using wordTrace_append hprefix tailTrace_665248
  have hstable : (prefixWord ++ tailWord_665248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665248).length < 2 ^ (prefixWord ++ tailWord_665248).sum := by decide
  have hdescent : baseEnd_665248 < baseStart_665248 := by decide
  rcases family_descends (prefixWord ++ tailWord_665248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665282 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_665282 : Nat := 118140960795 + 665282 * 2 ^ 59
def prefixEnd_665282 : Nat := 4983230072969 + 3 ^ 40 * 665282 * 2
def baseEnd_665282 : Nat := 227739624523047543210287

theorem tailTrace_665282 : CollatzResearch.WordTrace tailWord_665282 prefixEnd_665282 227739624523047543210287 := by
  unfold tailWord_665282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066206993951102491217525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16176551983869606643246733 6066206993951102491217525)
  ·
    refine ⟨568706905682915858551643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6066206993951102491217525 568706905682915858551643)
    ·
      refine ⟨853060358524373787827465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568706905682915858551643 853060358524373787827465)
      ·
        refine ⟨639795268893280340870599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 853060358524373787827465 639795268893280340870599)
        ·
          refine ⟨959692903339920511305899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639795268893280340870599 959692903339920511305899)
          ·
            refine ⟨1439539355009880766958849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959692903339920511305899 1439539355009880766958849)
            ·
              refine ⟨1079654516257410575219137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439539355009880766958849 1079654516257410575219137)
              ·
                refine ⟨809740887193057931414353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079654516257410575219137 809740887193057931414353)
                ·
                  refine ⟨607305665394793448560765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809740887193057931414353 607305665394793448560765)
                  ·
                    refine ⟨227739624523047543210287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607305665394793448560765 227739624523047543210287)
                    ·
                      rfl

theorem cell22_665282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_665282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665282 prefixEnd_665282 := by exact prefixLift 665282
  have htrace : WordTrace (prefixWord ++ tailWord_665282) baseStart_665282 baseEnd_665282 := by
    simpa [prefixWord, tailWord_665282, baseEnd_665282] using wordTrace_append hprefix tailTrace_665282
  have hstable : (prefixWord ++ tailWord_665282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665282).length < 2 ^ (prefixWord ++ tailWord_665282).sum := by decide
  have hdescent : baseEnd_665282 < baseStart_665282 := by decide
  rcases family_descends (prefixWord ++ tailWord_665282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665287 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 2, 5]
def baseStart_665287 : Nat := 118140960795 + 665287 * 2 ^ 59
def prefixEnd_665287 : Nat := 4983230072969 + 3 ^ 40 * 665287 * 2
def baseEnd_665287 : Nat := 227741336125229196835271

theorem tailTrace_665287 : CollatzResearch.WordTrace tailWord_665287 prefixEnd_665287 227741336125229196835271 := by
  unfold tailWord_665287
  simp only [CollatzResearch.WordTrace]
  refine ⟨24265010340786295818802115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16176673560524197212534743 24265010340786295818802115)
  ·
    refine ⟨36397515511179443728203173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24265010340786295818802115 36397515511179443728203173)
    ·
      refine ⟨6824534158346145699038095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36397515511179443728203173 6824534158346145699038095)
      ·
        refine ⟨10236801237519218548557143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6824534158346145699038095 10236801237519218548557143)
        ·
          refine ⟨15355201856278827822835715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10236801237519218548557143 15355201856278827822835715)
          ·
            refine ⟨23032802784418241734253573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15355201856278827822835715 23032802784418241734253573)
            ·
              refine ⟨4318650522078420325172545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23032802784418241734253573 4318650522078420325172545)
              ·
                refine ⟨3238987891558815243879409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4318650522078420325172545 3238987891558815243879409)
                ·
                  refine ⟨2429240918669111432909557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3238987891558815243879409 2429240918669111432909557)
                  ·
                    refine ⟨227741336125229196835271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2429240918669111432909557 227741336125229196835271)
                    ·
                      rfl

theorem cell22_665287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_665287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665287 prefixEnd_665287 := by exact prefixLift 665287
  have htrace : WordTrace (prefixWord ++ tailWord_665287) baseStart_665287 baseEnd_665287 := by
    simpa [prefixWord, tailWord_665287, baseEnd_665287] using wordTrace_append hprefix tailTrace_665287
  have hstable : (prefixWord ++ tailWord_665287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665287).length < 2 ^ (prefixWord ++ tailWord_665287).sum := by decide
  have hdescent : baseEnd_665287 < baseStart_665287 := by decide
  rcases family_descends (prefixWord ++ tailWord_665287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665351 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 6]
def baseStart_665351 : Nat := 118140960795 + 665351 * 2 ^ 59
def prefixEnd_665351 : Nat := 4983230072969 + 3 ^ 40 * 665351 * 2
def baseEnd_665351 : Nat := 75921081544384787745025

theorem tailTrace_665351 : CollatzResearch.WordTrace tailWord_665351 prefixEnd_665351 75921081544384787745025 := by
  unfold tailWord_665351
  simp only [CollatzResearch.WordTrace]
  refine ⟨24267344612554434749131907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16178229741702956499421271 24267344612554434749131907)
  ·
    refine ⟨36401016918831652123697861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24267344612554434749131907 36401016918831652123697861)
    ·
      refine ⟨6825190672280934773193349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36401016918831652123697861 6825190672280934773193349)
      ·
        refine ⟨1279723251052675269973753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6825190672280934773193349 1279723251052675269973753)
        ·
          refine ⟨959792438289506452480315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279723251052675269973753 959792438289506452480315)
          ·
            refine ⟨1439688657434259678720473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959792438289506452480315 1439688657434259678720473)
            ·
              refine ⟨1079766493075694759040355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439688657434259678720473 1079766493075694759040355)
              ·
                refine ⟨1619649739613542138560533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079766493075694759040355 1619649739613542138560533)
                ·
                  refine ⟨75921081544384787745025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1619649739613542138560533 75921081544384787745025)
                  ·
                    rfl

theorem cell22_665351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 6].length) (baseStart_665351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665351 prefixEnd_665351 := by exact prefixLift 665351
  have htrace : WordTrace (prefixWord ++ tailWord_665351) baseStart_665351 baseEnd_665351 := by
    simpa [prefixWord, tailWord_665351, baseEnd_665351] using wordTrace_append hprefix tailTrace_665351
  have hstable : (prefixWord ++ tailWord_665351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665351).length < 2 ^ (prefixWord ++ tailWord_665351).sum := by decide
  have hdescent : baseEnd_665351 < baseStart_665351 := by decide
  rcases family_descends (prefixWord ++ tailWord_665351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665379 : List Nat := [1, 1, 1, 4, 2, 1, 6, 6]
def baseStart_665379 : Nat := 118140960795 + 665379 * 2 ^ 59
def prefixEnd_665379 : Nat := 4983230072969 + 3 ^ 40 * 665379 * 2
def baseEnd_665379 : Nat := 25308092178374624837221

theorem tailTrace_665379 : CollatzResearch.WordTrace tailWord_665379 prefixEnd_665379 25308092178374624837221 := by
  unfold tailWord_665379
  simp only [CollatzResearch.WordTrace]
  refine ⟨24268365856452995531151191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16178910570968663687434127 24268365856452995531151191)
  ·
    refine ⟨36402548784679493296726787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24268365856452995531151191 36402548784679493296726787)
    ·
      refine ⟨54603823177019239945090181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36402548784679493296726787 54603823177019239945090181)
      ·
        refine ⟨10238216845691107489704409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54603823177019239945090181 10238216845691107489704409)
        ·
          refine ⟨7678662634268330617278307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10238216845691107489704409 7678662634268330617278307)
          ·
            refine ⟨11517993951402495925917461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7678662634268330617278307 11517993951402495925917461)
            ·
              refine ⟨539905966471991996527381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11517993951402495925917461 539905966471991996527381)
              ·
                refine ⟨25308092178374624837221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 539905966471991996527381 25308092178374624837221)
                ·
                  rfl

theorem cell22_665379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 6].length) (baseStart_665379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665379 prefixEnd_665379 := by exact prefixLift 665379
  have htrace : WordTrace (prefixWord ++ tailWord_665379) baseStart_665379 baseEnd_665379 := by
    simpa [prefixWord, tailWord_665379, baseEnd_665379] using wordTrace_append hprefix tailTrace_665379
  have hstable : (prefixWord ++ tailWord_665379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665379).length < 2 ^ (prefixWord ++ tailWord_665379).sum := by decide
  have hdescent : baseEnd_665379 < baseStart_665379 := by decide
  rcases family_descends (prefixWord ++ tailWord_665379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665392 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_665392 : Nat := 118140960795 + 665392 * 2 ^ 59
def prefixEnd_665392 : Nat := 4983230072969 + 3 ^ 40 * 665392 * 2
def baseEnd_665392 : Nat := 227777279771043922959949

theorem tailTrace_665392 : CollatzResearch.WordTrace tailWord_665392 prefixEnd_665392 227777279771043922959949 := by
  unfold tailWord_665392
  simp only [CollatzResearch.WordTrace]
  refine ⟨12134420002702949375687215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16179226670270599167582953 12134420002702949375687215)
  ·
    refine ⟨18201630004054424063530823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12134420002702949375687215 18201630004054424063530823)
    ·
      refine ⟨27302445006081636095296235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18201630004054424063530823 27302445006081636095296235)
      ·
        refine ⟨40953667509122454142944353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27302445006081636095296235 40953667509122454142944353)
        ·
          refine ⟨30715250631841840607208265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40953667509122454142944353 30715250631841840607208265)
          ·
            refine ⟨23036437973881380455406199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30715250631841840607208265 23036437973881380455406199)
            ·
              refine ⟨34554656960822070683109299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23036437973881380455406199 34554656960822070683109299)
              ·
                refine ⟨51831985441233106024663949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34554656960822070683109299 51831985441233106024663949)
                ·
                  refine ⟨19436994540462414759248981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51831985441233106024663949 19436994540462414759248981)
                  ·
                    refine ⟨227777279771043922959949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19436994540462414759248981 227777279771043922959949)
                    ·
                      rfl

theorem cell22_665392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_665392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665392 prefixEnd_665392 := by exact prefixLift 665392
  have htrace : WordTrace (prefixWord ++ tailWord_665392) baseStart_665392 baseEnd_665392 := by
    simpa [prefixWord, tailWord_665392, baseEnd_665392] using wordTrace_append hprefix tailTrace_665392
  have hstable : (prefixWord ++ tailWord_665392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665392).length < 2 ^ (prefixWord ++ tailWord_665392).sum := by decide
  have hdescent : baseEnd_665392 < baseStart_665392 := by decide
  rcases family_descends (prefixWord ++ tailWord_665392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665396 : List Nat := [2, 5, 1, 1, 2, 3, 8]
def baseStart_665396 : Nat := 118140960795 + 665396 * 2 ^ 59
def prefixEnd_665396 : Nat := 4983230072969 + 3 ^ 40 * 665396 * 2
def baseEnd_665396 : Nat := 8436246261214416513331

theorem tailTrace_665396 : CollatzResearch.WordTrace tailWord_665396 prefixEnd_665396 8436246261214416513331 := by
  unfold tailWord_665396
  simp only [CollatzResearch.WordTrace]
  refine ⟨12134492948695703717260021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16179323931594271623013361 12134492948695703717260021)
  ·
    refine ⟨1137608713940222223493127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12134492948695703717260021 1137608713940222223493127)
    ·
      refine ⟨1706413070910333335239691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137608713940222223493127 1706413070910333335239691)
      ·
        refine ⟨2559619606365500002859537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706413070910333335239691 2559619606365500002859537)
        ·
          refine ⟨1919714704774125002144653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559619606365500002859537 1919714704774125002144653)
          ·
            refine ⟨719893014290296875804245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1919714704774125002144653 719893014290296875804245)
            ·
              refine ⟨8436246261214416513331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 719893014290296875804245 8436246261214416513331)
              ·
                rfl

theorem cell22_665396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 8].length) (baseStart_665396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665396 prefixEnd_665396 := by exact prefixLift 665396
  have htrace : WordTrace (prefixWord ++ tailWord_665396) baseStart_665396 baseEnd_665396 := by
    simpa [prefixWord, tailWord_665396, baseEnd_665396] using wordTrace_append hprefix tailTrace_665396
  have hstable : (prefixWord ++ tailWord_665396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665396).length < 2 ^ (prefixWord ++ tailWord_665396).sum := by decide
  have hdescent : baseEnd_665396 < baseStart_665396 := by decide
  rcases family_descends (prefixWord ++ tailWord_665396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665398 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_665398 : Nat := 118140960795 + 665398 * 2 ^ 59
def prefixEnd_665398 : Nat := 4983230072969 + 3 ^ 40 * 665398 * 2
def baseEnd_665398 : Nat := 227779333693661907309931

theorem tailTrace_665398 : CollatzResearch.WordTrace tailWord_665398 prefixEnd_665398 227779333693661907309931 := by
  unfold tailWord_665398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516816177711510111005803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16179372562256107850728565 1516816177711510111005803)
  ·
    refine ⟨2275224266567265166508705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1516816177711510111005803 2275224266567265166508705)
    ·
      refine ⟨1706418199925448874881529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2275224266567265166508705 1706418199925448874881529)
      ·
        refine ⟨1279813649944086656161147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1706418199925448874881529 1279813649944086656161147)
        ·
          refine ⟨1919720474916129984241721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279813649944086656161147 1919720474916129984241721)
          ·
            refine ⟨1439790356187097488181291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919720474916129984241721 1439790356187097488181291)
            ·
              refine ⟨2159685534280646232271937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439790356187097488181291 2159685534280646232271937)
              ·
                refine ⟨1619764150710484674203953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159685534280646232271937 1619764150710484674203953)
                ·
                  refine ⟨1214823113032863505652965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1619764150710484674203953 1214823113032863505652965)
                  ·
                    refine ⟨227779333693661907309931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1214823113032863505652965 227779333693661907309931)
                    ·
                      rfl

theorem cell22_665398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_665398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665398 prefixEnd_665398 := by exact prefixLift 665398
  have htrace : WordTrace (prefixWord ++ tailWord_665398) baseStart_665398 baseEnd_665398 := by
    simpa [prefixWord, tailWord_665398, baseEnd_665398] using wordTrace_append hprefix tailTrace_665398
  have hstable : (prefixWord ++ tailWord_665398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665398).length < 2 ^ (prefixWord ++ tailWord_665398).sum := by decide
  have hdescent : baseEnd_665398 < baseStart_665398 := by decide
  rcases family_descends (prefixWord ++ tailWord_665398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665411 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 3, 3]
def baseStart_665411 : Nat := 118140960795 + 665411 * 2 ^ 59
def prefixEnd_665411 : Nat := 4983230072969 + 3 ^ 40 * 665411 * 2
def baseEnd_665411 : Nat := 227783783859334206734891

theorem tailTrace_665411 : CollatzResearch.WordTrace tailWord_665411 prefixEnd_665411 227783783859334206734891 := by
  unfold tailWord_665411
  simp only [CollatzResearch.WordTrace]
  refine ⟨24269532992337064996316087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16179688661558043330877391 24269532992337064996316087)
  ·
    refine ⟨36404299488505597494474131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24269532992337064996316087 36404299488505597494474131)
    ·
      refine ⟨54606449232758396241711197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36404299488505597494474131 54606449232758396241711197)
      ·
        refine ⟨20477418462284398590641699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54606449232758396241711197 20477418462284398590641699)
        ·
          refine ⟨30716127693426597885962549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20477418462284398590641699 30716127693426597885962549)
          ·
            refine ⟨2879636971258743551808989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30716127693426597885962549 2879636971258743551808989)
            ·
              refine ⟨1079863864222028831928371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2879636971258743551808989 1079863864222028831928371)
              ·
                refine ⟨1619795796333043247892557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079863864222028831928371 1619795796333043247892557)
                ·
                  refine ⟨607423423624891217959709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1619795796333043247892557 607423423624891217959709)
                  ·
                    refine ⟨227783783859334206734891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607423423624891217959709 227783783859334206734891)
                    ·
                      rfl

theorem cell22_665411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 3].length) (baseStart_665411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665411 prefixEnd_665411 := by exact prefixLift 665411
  have htrace : WordTrace (prefixWord ++ tailWord_665411) baseStart_665411 baseEnd_665411 := by
    simpa [prefixWord, tailWord_665411, baseEnd_665411] using wordTrace_append hprefix tailTrace_665411
  have hstable : (prefixWord ++ tailWord_665411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665411).length < 2 ^ (prefixWord ++ tailWord_665411).sum := by decide
  have hdescent : baseEnd_665411 < baseStart_665411 := by decide
  rcases family_descends (prefixWord ++ tailWord_665411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665462 : List Nat := [5, 1, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_665462 : Nat := 118140960795 + 665462 * 2 ^ 59
def prefixEnd_665462 : Nat := 4983230072969 + 3 ^ 40 * 665462 * 2
def baseEnd_665462 : Nat := 227801242201587073709735

theorem tailTrace_665462 : CollatzResearch.WordTrace tailWord_665462 prefixEnd_665462 227801242201587073709735 := by
  unfold tailWord_665462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516962069697018794151415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16180928743434867137615093 1516962069697018794151415)
  ·
    refine ⟨2275443104545528191227123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1516962069697018794151415 2275443104545528191227123)
    ·
      refine ⟨3413164656818292286840685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2275443104545528191227123 3413164656818292286840685)
      ·
        refine ⟨1279936746306859607565257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3413164656818292286840685 1279936746306859607565257)
        ·
          refine ⟨959952559730144705673943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279936746306859607565257 959952559730144705673943)
          ·
            refine ⟨1439928839595217058510915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959952559730144705673943 1439928839595217058510915)
            ·
              refine ⟨2159893259392825587766373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439928839595217058510915 2159893259392825587766373)
              ·
                refine ⟨404979986136154797706195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2159893259392825587766373 404979986136154797706195)
                ·
                  refine ⟨607469979204232196559293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404979986136154797706195 607469979204232196559293)
                  ·
                    refine ⟨227801242201587073709735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607469979204232196559293 227801242201587073709735)
                    ·
                      rfl

theorem cell22_665462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_665462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665462 prefixEnd_665462 := by exact prefixLift 665462
  have htrace : WordTrace (prefixWord ++ tailWord_665462) baseStart_665462 baseEnd_665462 := by
    simpa [prefixWord, tailWord_665462, baseEnd_665462] using wordTrace_append hprefix tailTrace_665462
  have hstable : (prefixWord ++ tailWord_665462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665462).length < 2 ^ (prefixWord ++ tailWord_665462).sum := by decide
  have hdescent : baseEnd_665462 < baseStart_665462 := by decide
  rcases family_descends (prefixWord ++ tailWord_665462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665469 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 6]
def baseStart_665469 : Nat := 118140960795 + 665469 * 2 ^ 59
def prefixEnd_665469 : Nat := 4983230072969 + 3 ^ 40 * 665469 * 2
def baseEnd_665469 : Nat := 75934546148213796261571

theorem tailTrace_665469 : CollatzResearch.WordTrace tailWord_665469 prefixEnd_665469 75934546148213796261571 := by
  unfold tailWord_665469
  simp only [CollatzResearch.WordTrace]
  refine ⟨24271648426126940901927461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16181098950751293934618307 24271648426126940901927461)
  ·
    refine ⟨4550934079898801419111399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24271648426126940901927461 4550934079898801419111399)
    ·
      refine ⟨6826401119848202128667099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4550934079898801419111399 6826401119848202128667099)
      ·
        refine ⟨10239601679772303193000649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6826401119848202128667099 10239601679772303193000649)
        ·
          refine ⟨7679701259829227394750487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10239601679772303193000649 7679701259829227394750487)
          ·
            refine ⟨11519551889743841092125731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7679701259829227394750487 11519551889743841092125731)
            ·
              refine ⟨17279327834615761638188597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11519551889743841092125731 17279327834615761638188597)
              ·
                refine ⟨1619936984495227653580181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17279327834615761638188597 1619936984495227653580181)
                ·
                  refine ⟨75934546148213796261571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1619936984495227653580181 75934546148213796261571)
                  ·
                    rfl

theorem cell22_665469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_665469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665469 prefixEnd_665469 := by exact prefixLift 665469
  have htrace : WordTrace (prefixWord ++ tailWord_665469) baseStart_665469 baseEnd_665469 := by
    simpa [prefixWord, tailWord_665469, baseEnd_665469] using wordTrace_append hprefix tailTrace_665469
  have hstable : (prefixWord ++ tailWord_665469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665469).length < 2 ^ (prefixWord ++ tailWord_665469).sum := by decide
  have hdescent : baseEnd_665469 < baseStart_665469 := by decide
  rcases family_descends (prefixWord ++ tailWord_665469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665473 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 2, 5]
def baseStart_665473 : Nat := 118140960795 + 665473 * 2 ^ 59
def prefixEnd_665473 : Nat := 4983230072969 + 3 ^ 40 * 665473 * 2
def baseEnd_665473 : Nat := 227805007726386711684701

theorem tailTrace_665473 : CollatzResearch.WordTrace tailWord_665473 prefixEnd_665473 227805007726386711684701 := by
  unfold tailWord_665473
  simp only [CollatzResearch.WordTrace]
  refine ⟨24271794318112449585073073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16181196212074966390048715 24271794318112449585073073)
  ·
    refine ⟨18203845738584337188804805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24271794318112449585073073 18203845738584337188804805)
    ·
      refine ⟨3413221075984563222900901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18203845738584337188804805 3413221075984563222900901)
      ·
        refine ⟨639978951747105604293919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3413221075984563222900901 639978951747105604293919)
        ·
          refine ⟨959968427620658406440879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639978951747105604293919 959968427620658406440879)
          ·
            refine ⟨1439952641430987609661319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959968427620658406440879 1439952641430987609661319)
            ·
              refine ⟨2159928962146481414491979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439952641430987609661319 2159928962146481414491979)
              ·
                refine ⟨3239893443219722121737969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159928962146481414491979 3239893443219722121737969)
                ·
                  refine ⟨2429920082414791591303477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3239893443219722121737969 2429920082414791591303477)
                  ·
                    refine ⟨227805007726386711684701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2429920082414791591303477 227805007726386711684701)
                    ·
                      rfl

theorem cell22_665473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_665473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665473 prefixEnd_665473 := by exact prefixLift 665473
  have htrace : WordTrace (prefixWord ++ tailWord_665473) baseStart_665473 baseEnd_665473 := by
    simpa [prefixWord, tailWord_665473, baseEnd_665473] using wordTrace_append hprefix tailTrace_665473
  have hstable : (prefixWord ++ tailWord_665473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665473).length < 2 ^ (prefixWord ++ tailWord_665473).sum := by decide
  have hdescent : baseEnd_665473 < baseStart_665473 := by decide
  rcases family_descends (prefixWord ++ tailWord_665473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665501 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_665501 : Nat := 118140960795 + 665501 * 2 ^ 59
def prefixEnd_665501 : Nat := 4983230072969 + 3 ^ 40 * 665501 * 2
def baseEnd_665501 : Nat := 227814592698603971984615

theorem tailTrace_665501 : CollatzResearch.WordTrace tailWord_665501 prefixEnd_665501 227814592698603971984615 := by
  unfold tailWord_665501
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272815562011010367092357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16181877041340673578061571 24272815562011010367092357)
  ·
    refine ⟨4551152917877064443829817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24272815562011010367092357 4551152917877064443829817)
    ·
      refine ⟨3413364688407798332872363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4551152917877064443829817 3413364688407798332872363)
      ·
        refine ⟨5120047032611697499308545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413364688407798332872363 5120047032611697499308545)
        ·
          refine ⟨3840035274458773124481409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5120047032611697499308545 3840035274458773124481409)
          ·
            refine ⟨2880026455844079843361057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3840035274458773124481409 2880026455844079843361057)
            ·
              refine ⟨2160019841883059882520793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880026455844079843361057 2160019841883059882520793)
              ·
                refine ⟨1620014881412294911890595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160019841883059882520793 1620014881412294911890595)
                ·
                  refine ⟨2430022322118442367835893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620014881412294911890595 2430022322118442367835893)
                  ·
                    refine ⟨227814592698603971984615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2430022322118442367835893 227814592698603971984615)
                    ·
                      rfl

theorem cell22_665501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_665501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665501 prefixEnd_665501 := by exact prefixLift 665501
  have htrace : WordTrace (prefixWord ++ tailWord_665501) baseStart_665501 baseEnd_665501 := by
    simpa [prefixWord, tailWord_665501, baseEnd_665501] using wordTrace_append hprefix tailTrace_665501
  have hstable : (prefixWord ++ tailWord_665501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665501).length < 2 ^ (prefixWord ++ tailWord_665501).sum := by decide
  have hdescent : baseEnd_665501 < baseStart_665501 := by decide
  rcases family_descends (prefixWord ++ tailWord_665501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665548 : List Nat := [2, 2, 1, 4, 1, 4, 2, 6]
def baseStart_665548 : Nat := 118140960795 + 665548 * 2 ^ 59
def prefixEnd_665548 : Nat := 4983230072969 + 3 ^ 40 * 665548 * 2
def baseEnd_665548 : Nat := 25314520195456835117719

theorem tailTrace_665548 : CollatzResearch.WordTrace tailWord_665548 prefixEnd_665548 25314520195456835117719 := by
  unfold tailWord_665548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137264896420368697026649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16183019861893824929368865 12137264896420368697026649)
  ·
    refine ⟨9102948672315276522769987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12137264896420368697026649 9102948672315276522769987)
    ·
      refine ⟨13654423008472914784154981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9102948672315276522769987 13654423008472914784154981)
      ·
        refine ⟨2560204314088671522029059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13654423008472914784154981 2560204314088671522029059)
        ·
          refine ⟨3840306471133007283043589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560204314088671522029059 3840306471133007283043589)
          ·
            refine ⟨720057463337438865570673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3840306471133007283043589 720057463337438865570673)
            ·
              refine ⟨540043097503079149178005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720057463337438865570673 540043097503079149178005)
              ·
                refine ⟨25314520195456835117719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 540043097503079149178005 25314520195456835117719)
                ·
                  rfl

theorem cell22_665548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 6].length) (baseStart_665548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665548 prefixEnd_665548 := by exact prefixLift 665548
  have htrace : WordTrace (prefixWord ++ tailWord_665548) baseStart_665548 baseEnd_665548 := by
    simpa [prefixWord, tailWord_665548, baseEnd_665548] using wordTrace_append hprefix tailTrace_665548
  have hstable : (prefixWord ++ tailWord_665548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665548).length < 2 ^ (prefixWord ++ tailWord_665548).sum := by decide
  have hdescent : baseEnd_665548 < baseStart_665548 := by decide
  rcases family_descends (prefixWord ++ tailWord_665548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665559 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 9]
def baseStart_665559 : Nat := 118140960795 + 665559 * 2 ^ 59
def prefixEnd_665559 : Nat := 4983230072969 + 3 ^ 40 * 665559 * 2
def baseEnd_665559 : Nat := 75944815761303718011479

theorem tailTrace_665559 : CollatzResearch.WordTrace tailWord_665559 prefixEnd_665559 75944815761303718011479 := by
  unfold tailWord_665559
  simp only [CollatzResearch.WordTrace]
  refine ⟨24274930995800886272703731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16183287330533924181802487 24274930995800886272703731)
  ·
    refine ⟨36412396493701329409055597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24274930995800886272703731 36412396493701329409055597)
    ·
      refine ⟨13654648685137998528395849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36412396493701329409055597 13654648685137998528395849)
      ·
        refine ⟨10240986513853498896296887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13654648685137998528395849 10240986513853498896296887)
        ·
          refine ⟨15361479770780248344445331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10240986513853498896296887 15361479770780248344445331)
          ·
            refine ⟨23042219656170372516667997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15361479770780248344445331 23042219656170372516667997)
            ·
              refine ⟨8640832371063889693750499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23042219656170372516667997 8640832371063889693750499)
              ·
                refine ⟨12961248556595834540625749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8640832371063889693750499 12961248556595834540625749)
                ·
                  refine ⟨75944815761303718011479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12961248556595834540625749 75944815761303718011479)
                  ·
                    rfl

theorem cell22_665559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 9].length) (baseStart_665559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665559 prefixEnd_665559 := by exact prefixLift 665559
  have htrace : WordTrace (prefixWord ++ tailWord_665559) baseStart_665559 baseEnd_665559 := by
    simpa [prefixWord, tailWord_665559, baseEnd_665559] using wordTrace_append hprefix tailTrace_665559
  have hstable : (prefixWord ++ tailWord_665559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665559).length < 2 ^ (prefixWord ++ tailWord_665559).sum := by decide
  have hdescent : baseEnd_665559 < baseStart_665559 := by decide
  rcases family_descends (prefixWord ++ tailWord_665559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665576 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 5]
def baseStart_665576 : Nat := 118140960795 + 665576 * 2 ^ 59
def prefixEnd_665576 : Nat := 4983230072969 + 3 ^ 40 * 665576 * 2
def baseEnd_665576 : Nat := 75946755577109592119795

theorem tailTrace_665576 : CollatzResearch.WordTrace tailWord_665576 prefixEnd_665576 75946755577109592119795 := by
  unfold tailWord_665576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137775518369649088036291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16183700691159532117381721 12137775518369649088036291)
  ·
    refine ⟨18206663277554473632054437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12137775518369649088036291 18206663277554473632054437)
    ·
      refine ⟨3413749364541463806010207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18206663277554473632054437 3413749364541463806010207)
      ·
        refine ⟨5120624046812195709015311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413749364541463806010207 5120624046812195709015311)
        ·
          refine ⟨7680936070218293563522967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120624046812195709015311 7680936070218293563522967)
          ·
            refine ⟨11521404105327440345284451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7680936070218293563522967 11521404105327440345284451)
            ·
              refine ⟨17282106157991160517926677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11521404105327440345284451 17282106157991160517926677)
              ·
                refine ⟨810098726155835649277813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17282106157991160517926677 810098726155835649277813)
                ·
                  refine ⟨75946755577109592119795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810098726155835649277813 75946755577109592119795)
                  ·
                    rfl

theorem cell22_665576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_665576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665576 prefixEnd_665576 := by exact prefixLift 665576
  have htrace : WordTrace (prefixWord ++ tailWord_665576) baseStart_665576 baseEnd_665576 := by
    simpa [prefixWord, tailWord_665576, baseEnd_665576] using wordTrace_append hprefix tailTrace_665576
  have hstable : (prefixWord ++ tailWord_665576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665576).length < 2 ^ (prefixWord ++ tailWord_665576).sum := by decide
  have hdescent : baseEnd_665576 < baseStart_665576 := by decide
  rcases family_descends (prefixWord ++ tailWord_665576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665593 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 5]
def baseStart_665593 : Nat := 118140960795 + 665593 * 2 ^ 59
def prefixEnd_665593 : Nat := 4983230072969 + 3 ^ 40 * 665593 * 2
def baseEnd_665593 : Nat := 75948695392915466228111

theorem tailTrace_665593 : CollatzResearch.WordTrace tailWord_665593 prefixEnd_665593 75948695392915466228111 := by
  unfold tailWord_665593
  simp only [CollatzResearch.WordTrace]
  refine ⟨24276171077677710079441433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16184114051785140052960955 24276171077677710079441433)
  ·
    refine ⟨18207128308258282559581075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24276171077677710079441433 18207128308258282559581075)
    ·
      refine ⟨27310692462387423839371613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18207128308258282559581075 27310692462387423839371613)
      ·
        refine ⟨10241509673395283939764355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27310692462387423839371613 10241509673395283939764355)
        ·
          refine ⟨15362264510092925909646533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10241509673395283939764355 15362264510092925909646533)
          ·
            refine ⟨2880424595642423608058725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15362264510092925909646533 2880424595642423608058725)
            ·
              refine ⟨540079611682954426511011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2880424595642423608058725 540079611682954426511011)
              ·
                refine ⟨810119417524431639766517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540079611682954426511011 810119417524431639766517)
                ·
                  refine ⟨75948695392915466228111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810119417524431639766517 75948695392915466228111)
                  ·
                    rfl

theorem cell22_665593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_665593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665593 prefixEnd_665593 := by exact prefixLift 665593
  have htrace : WordTrace (prefixWord ++ tailWord_665593) baseStart_665593 baseEnd_665593 := by
    simpa [prefixWord, tailWord_665593, baseEnd_665593] using wordTrace_append hprefix tailTrace_665593
  have hstable : (prefixWord ++ tailWord_665593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665593).length < 2 ^ (prefixWord ++ tailWord_665593).sum := by decide
  have hdescent : baseEnd_665593 < baseStart_665593 := by decide
  rcases family_descends (prefixWord ++ tailWord_665593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665651 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 4, 4]
def baseStart_665651 : Nat := 118140960795 + 665651 * 2 ^ 59
def prefixEnd_665651 : Nat := 4983230072969 + 3 ^ 40 * 665651 * 2
def baseEnd_665651 : Nat := 227865940764053580734155

theorem tailTrace_665651 : CollatzResearch.WordTrace tailWord_665651 prefixEnd_665651 227865940764053580734155 := by
  unfold tailWord_665651
  simp only [CollatzResearch.WordTrace]
  refine ⟨24278286511467585985052807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16185524340978390656701871 24278286511467585985052807)
  ·
    refine ⟨36417429767201378977579211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24278286511467585985052807 36417429767201378977579211)
    ·
      refine ⟨54626144650802068466368817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36417429767201378977579211 54626144650802068466368817)
      ·
        refine ⟨40969608488101551349776613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54626144650802068466368817 40969608488101551349776613)
        ·
          refine ⟨7681801591519040878083115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40969608488101551349776613 7681801591519040878083115)
          ·
            refine ⟨11522702387278561317124673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7681801591519040878083115 11522702387278561317124673)
            ·
              refine ⟨8642026790458920987843505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11522702387278561317124673 8642026790458920987843505)
              ·
                refine ⟨6481520092844190740882629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8642026790458920987843505 6481520092844190740882629)
                ·
                  refine ⟨1215285017408285763915493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6481520092844190740882629 1215285017408285763915493)
                  ·
                    refine ⟨227865940764053580734155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1215285017408285763915493 227865940764053580734155)
                    ·
                      rfl

theorem cell22_665651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 4].length) (baseStart_665651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665651 prefixEnd_665651 := by exact prefixLift 665651
  have htrace : WordTrace (prefixWord ++ tailWord_665651) baseStart_665651 baseEnd_665651 := by
    simpa [prefixWord, tailWord_665651, baseEnd_665651] using wordTrace_append hprefix tailTrace_665651
  have hstable : (prefixWord ++ tailWord_665651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665651).length < 2 ^ (prefixWord ++ tailWord_665651).sum := by decide
  have hdescent : baseEnd_665651 < baseStart_665651 := by decide
  rcases family_descends (prefixWord ++ tailWord_665651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665670 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_665670 : Nat := 118140960795 + 665670 * 2 ^ 59
def prefixEnd_665670 : Nat := 4983230072969 + 3 ^ 40 * 665670 * 2
def baseEnd_665670 : Nat := 227872444852343864509097

theorem tailTrace_665670 : CollatzResearch.WordTrace tailWord_665670 prefixEnd_665670 227872444852343864509097 := by
  unfold tailWord_665670
  simp only [CollatzResearch.WordTrace]
  refine ⟨758718109324961007187327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16185986332265834819996309 758718109324961007187327)
  ·
    refine ⟨1138077163987441510780991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758718109324961007187327 1138077163987441510780991)
    ·
      refine ⟨1707115745981162266171487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138077163987441510780991 1707115745981162266171487)
      ·
        refine ⟨2560673618971743399257231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707115745981162266171487 2560673618971743399257231)
        ·
          refine ⟨3841010428457615098885847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560673618971743399257231 3841010428457615098885847)
          ·
            refine ⟨5761515642686422648328771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3841010428457615098885847 5761515642686422648328771)
            ·
              refine ⟨8642273464029633972493157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5761515642686422648328771 8642273464029633972493157)
              ·
                refine ⟨1620426274505556369842467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8642273464029633972493157 1620426274505556369842467)
                ·
                  refine ⟨2430639411758334554763701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620426274505556369842467 2430639411758334554763701)
                  ·
                    refine ⟨227872444852343864509097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2430639411758334554763701 227872444852343864509097)
                    ·
                      rfl

theorem cell22_665670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_665670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665670 prefixEnd_665670 := by exact prefixLift 665670
  have htrace : WordTrace (prefixWord ++ tailWord_665670) baseStart_665670 baseEnd_665670 := by
    simpa [prefixWord, tailWord_665670, baseEnd_665670] using wordTrace_append hprefix tailTrace_665670
  have hstable : (prefixWord ++ tailWord_665670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665670).length < 2 ^ (prefixWord ++ tailWord_665670).sum := by decide
  have hdescent : baseEnd_665670 < baseStart_665670 := by decide
  rcases family_descends (prefixWord ++ tailWord_665670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665762 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_665762 : Nat := 118140960795 + 665762 * 2 ^ 59
def prefixEnd_665762 : Nat := 4983230072969 + 3 ^ 40 * 665762 * 2
def baseEnd_665762 : Nat := 75967979444162097069605

theorem tailTrace_665762 : CollatzResearch.WordTrace tailWord_665762 prefixEnd_665762 75967979444162097069605 := by
  unfold tailWord_665762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6070583753516362985585885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16188223342710301294895693 6070583753516362985585885)
  ·
    refine ⟨2276468907568636119594707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6070583753516362985585885 2276468907568636119594707)
    ·
      refine ⟨3414703361352954179392061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2276468907568636119594707 3414703361352954179392061)
      ·
        refine ⟨1280513760507357817272023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3414703361352954179392061 1280513760507357817272023)
        ·
          refine ⟨1920770640761036725908035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280513760507357817272023 1920770640761036725908035)
          ·
            refine ⟨2881155961141555088862053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920770640761036725908035 2881155961141555088862053)
            ·
              refine ⟨540216742714041579161635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2881155961141555088862053 540216742714041579161635)
              ·
                refine ⟨810325114071062368742453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540216742714041579161635 810325114071062368742453)
                ·
                  refine ⟨75967979444162097069605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810325114071062368742453 75967979444162097069605)
                  ·
                    rfl

theorem cell22_665762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_665762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665762 prefixEnd_665762 := by exact prefixLift 665762
  have htrace : WordTrace (prefixWord ++ tailWord_665762) baseStart_665762 baseEnd_665762 := by
    simpa [prefixWord, tailWord_665762, baseEnd_665762] using wordTrace_append hprefix tailTrace_665762
  have hstable : (prefixWord ++ tailWord_665762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665762).length < 2 ^ (prefixWord ++ tailWord_665762).sum := by decide
  have hdescent : baseEnd_665762 < baseStart_665762 := by decide
  rcases family_descends (prefixWord ++ tailWord_665762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665792 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 1, 4]
def baseStart_665792 : Nat := 118140960795 + 665792 * 2 ^ 59
def prefixEnd_665792 : Nat := 4983230072969 + 3 ^ 40 * 665792 * 2
def baseEnd_665792 : Nat := 227914207945576212958723

theorem tailTrace_665792 : CollatzResearch.WordTrace tailWord_665792 prefixEnd_665792 227914207945576212958723 := by
  unfold tailWord_665792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12141714601978383532967815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16188952802637844710623753 12141714601978383532967815)
  ·
    refine ⟨18212571902967575299451723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12141714601978383532967815 18212571902967575299451723)
    ·
      refine ⟨27318857854451362949177585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18212571902967575299451723 27318857854451362949177585)
      ·
        refine ⟨20489143390838522211883189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27318857854451362949177585 20489143390838522211883189)
        ·
          refine ⟨1920857192891111457364049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20489143390838522211883189 1920857192891111457364049)
          ·
            refine ⟨1440642894668333593023037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1920857192891111457364049 1440642894668333593023037)
            ·
              refine ⟨540241085500625097383639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1440642894668333593023037 540241085500625097383639)
              ·
                refine ⟨810361628250937646075459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540241085500625097383639 810361628250937646075459)
                ·
                  refine ⟨1215542442376406469113189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810361628250937646075459 1215542442376406469113189)
                  ·
                    refine ⟨227914207945576212958723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1215542442376406469113189 227914207945576212958723)
                    ·
                      rfl

theorem cell22_665792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 4].length) (baseStart_665792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665792 prefixEnd_665792 := by exact prefixLift 665792
  have htrace : WordTrace (prefixWord ++ tailWord_665792) baseStart_665792 baseEnd_665792 := by
    simpa [prefixWord, tailWord_665792, baseEnd_665792] using wordTrace_append hprefix tailTrace_665792
  have hstable : (prefixWord ++ tailWord_665792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665792).length < 2 ^ (prefixWord ++ tailWord_665792).sum := by decide
  have hdescent : baseEnd_665792 < baseStart_665792 := by decide
  rcases family_descends (prefixWord ++ tailWord_665792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665803 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 2, 4]
def baseStart_665803 : Nat := 118140960795 + 665803 * 2 ^ 59
def prefixEnd_665803 : Nat := 4983230072969 + 3 ^ 40 * 665803 * 2
def baseEnd_665803 : Nat := 227917973470375850933689

theorem tailTrace_665803 : CollatzResearch.WordTrace tailWord_665803 prefixEnd_665803 227917973470375850933689 := by
  unfold tailWord_665803
  simp only [CollatzResearch.WordTrace]
  refine ⟨24283830406916915944586063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16189220271277943963057375 24283830406916915944586063)
  ·
    refine ⟨36425745610375373916879095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24283830406916915944586063 36425745610375373916879095)
    ·
      refine ⟨54638618415563060875318643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36425745610375373916879095 54638618415563060875318643)
      ·
        refine ⟨81957927623344591312977965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54638618415563060875318643 81957927623344591312977965)
        ·
          refine ⟨30734222858754221742366737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81957927623344591312977965 30734222858754221742366737)
          ·
            refine ⟨23050667144065666306775053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30734222858754221742366737 23050667144065666306775053)
            ·
              refine ⟨8644000179024624865040645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23050667144065666306775053 8644000179024624865040645)
              ·
                refine ⟨1620750033567117162195121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8644000179024624865040645 1620750033567117162195121)
                ·
                  refine ⟨1215562525175337871646341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1620750033567117162195121 1215562525175337871646341)
                  ·
                    refine ⟨227917973470375850933689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1215562525175337871646341 227917973470375850933689)
                    ·
                      rfl

theorem cell22_665803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 4].length) (baseStart_665803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665803 prefixEnd_665803 := by exact prefixLift 665803
  have htrace : WordTrace (prefixWord ++ tailWord_665803) baseStart_665803 baseEnd_665803 := by
    simpa [prefixWord, tailWord_665803, baseEnd_665803] using wordTrace_append hprefix tailTrace_665803
  have hstable : (prefixWord ++ tailWord_665803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665803).length < 2 ^ (prefixWord ++ tailWord_665803).sum := by decide
  have hdescent : baseEnd_665803 < baseStart_665803 := by decide
  rcases family_descends (prefixWord ++ tailWord_665803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665818 : List Nat := [3, 1, 1, 2, 2, 1, 5, 7]
def baseStart_665818 : Nat := 118140960795 + 665818 * 2 ^ 59
def prefixEnd_665818 : Nat := 4983230072969 + 3 ^ 40 * 665818 * 2
def baseEnd_665818 : Nat := 25324789808546756867627

theorem tailTrace_665818 : CollatzResearch.WordTrace tailWord_665818 prefixEnd_665818 25324789808546756867627 := by
  unfold tailWord_665818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071094375465643376595527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16189585001241715670921405 6071094375465643376595527)
  ·
    refine ⟨9106641563198465064893291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6071094375465643376595527 9106641563198465064893291)
    ·
      refine ⟨13659962344797697597339937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9106641563198465064893291 13659962344797697597339937)
      ·
        refine ⟨10244971758598273198004953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13659962344797697597339937 10244971758598273198004953)
        ·
          refine ⟨7683728818948704898503715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10244971758598273198004953 7683728818948704898503715)
          ·
            refine ⟨11525593228423057347755573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7683728818948704898503715 11525593228423057347755573)
            ·
              refine ⟨1080524365164661626352085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11525593228423057347755573 1080524365164661626352085)
              ·
                refine ⟨25324789808546756867627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1080524365164661626352085 25324789808546756867627)
                ·
                  rfl

theorem cell22_665818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_665818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665818 prefixEnd_665818 := by exact prefixLift 665818
  have htrace : WordTrace (prefixWord ++ tailWord_665818) baseStart_665818 baseEnd_665818 := by
    simpa [prefixWord, tailWord_665818, baseEnd_665818] using wordTrace_append hprefix tailTrace_665818
  have hstable : (prefixWord ++ tailWord_665818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665818).length < 2 ^ (prefixWord ++ tailWord_665818).sum := by decide
  have hdescent : baseEnd_665818 < baseStart_665818 := by decide
  rcases family_descends (prefixWord ++ tailWord_665818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665867 : List Nat := [1, 1, 1, 1, 5, 2, 1, 6, 1, 3]
def baseStart_665867 : Nat := 118140960795 + 665867 * 2 ^ 59
def prefixEnd_665867 : Nat := 4983230072969 + 3 ^ 40 * 665867 * 2
def baseEnd_665867 : Nat := 227939881978301017333493

theorem tailTrace_665867 : CollatzResearch.WordTrace tailWord_665867 prefixEnd_665867 227939881978301017333493 := by
  unfold tailWord_665867
  simp only [CollatzResearch.WordTrace]
  refine ⟨24286164678685054874915855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16190776452456703249943903 24286164678685054874915855)
  ·
    refine ⟨36429247018027582312373783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24286164678685054874915855 36429247018027582312373783)
    ·
      refine ⟨54643870527041373468560675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36429247018027582312373783 54643870527041373468560675)
      ·
        refine ⟨81965805790562060202841013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54643870527041373468560675 81965805790562060202841013)
        ·
          refine ⟨7684294292865193144016345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81965805790562060202841013 7684294292865193144016345)
          ·
            refine ⟨5763220719648894858012259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7684294292865193144016345 5763220719648894858012259)
            ·
              refine ⟨8644831079473342287018389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5763220719648894858012259 8644831079473342287018389)
              ·
                refine ⟨405226456850312919703987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8644831079473342287018389 405226456850312919703987)
                ·
                  refine ⟨607839685275469379555981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405226456850312919703987 607839685275469379555981)
                  ·
                    refine ⟨227939881978301017333493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607839685275469379555981 227939881978301017333493)
                    ·
                      rfl

theorem cell22_665867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 1, 3].length) (baseStart_665867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665867 prefixEnd_665867 := by exact prefixLift 665867
  have htrace : WordTrace (prefixWord ++ tailWord_665867) baseStart_665867 baseEnd_665867 := by
    simpa [prefixWord, tailWord_665867, baseEnd_665867] using wordTrace_append hprefix tailTrace_665867
  have hstable : (prefixWord ++ tailWord_665867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665867).length < 2 ^ (prefixWord ++ tailWord_665867).sum := by decide
  have hdescent : baseEnd_665867 < baseStart_665867 := by decide
  rcases family_descends (prefixWord ++ tailWord_665867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665987 : List Nat := [1, 1, 1, 3, 6, 2, 1, 7]
def baseStart_665987 : Nat := 118140960795 + 665987 * 2 ^ 59
def prefixEnd_665987 : Nat := 4983230072969 + 3 ^ 40 * 665987 * 2
def baseEnd_665987 : Nat := 25331217825628967148125

theorem tailTrace_665987 : CollatzResearch.WordTrace tailWord_665987 prefixEnd_665987 25331217825628967148125 := by
  unfold tailWord_665987
  simp only [CollatzResearch.WordTrace]
  refine ⟨24290541438250315369284215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16193694292166876912856143 24290541438250315369284215)
  ·
    refine ⟨36435812157375473053926323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24290541438250315369284215 36435812157375473053926323)
    ·
      refine ⟨54653718236063209580889485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36435812157375473053926323 54653718236063209580889485)
      ·
        refine ⟨20495144338523703592833557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54653718236063209580889485 20495144338523703592833557)
        ·
          refine ⟨960709890868298605914073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20495144338523703592833557 960709890868298605914073)
          ·
            refine ⟨720532418151223954435555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960709890868298605914073 720532418151223954435555)
            ·
              refine ⟨1080798627226835931653333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720532418151223954435555 1080798627226835931653333)
              ·
                refine ⟨25331217825628967148125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1080798627226835931653333 25331217825628967148125)
                ·
                  rfl

theorem cell22_665987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 7].length) (baseStart_665987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_665987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_665987 prefixEnd_665987 := by exact prefixLift 665987
  have htrace : WordTrace (prefixWord ++ tailWord_665987) baseStart_665987 baseEnd_665987 := by
    simpa [prefixWord, tailWord_665987, baseEnd_665987] using wordTrace_append hprefix tailTrace_665987
  have hstable : (prefixWord ++ tailWord_665987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665987).length < 2 ^ (prefixWord ++ tailWord_665987).sum := by decide
  have hdescent : baseEnd_665987 < baseStart_665987 := by decide
  rcases family_descends (prefixWord ++ tailWord_665987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666004 : List Nat := [2, 4, 2, 1, 3, 1, 3, 6]
def baseStart_666004 : Nat := 118140960795 + 666004 * 2 ^ 59
def prefixEnd_666004 : Nat := 4983230072969 + 3 ^ 40 * 666004 * 2
def baseEnd_666004 : Nat := 25331864430897591850897

theorem tailTrace_666004 : CollatzResearch.WordTrace tailWord_666004 prefixEnd_666004 25331864430897591850897 := by
  unfold tailWord_666004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12145580739594363636326533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16194107652792484848435377 12145580739594363636326533)
  ·
    refine ⟨2277296388673943181811225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12145580739594363636326533 2277296388673943181811225)
    ·
      refine ⟨1707972291505457386358419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2277296388673943181811225 1707972291505457386358419)
      ·
        refine ⟨2561958437258186079537629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707972291505457386358419 2561958437258186079537629)
        ·
          refine ⟨960734413971819779826611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2561958437258186079537629 960734413971819779826611)
          ·
            refine ⟨1441101620957729669739917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960734413971819779826611 1441101620957729669739917)
            ·
              refine ⟨540413107859148626152469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1441101620957729669739917 540413107859148626152469)
              ·
                refine ⟨25331864430897591850897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 540413107859148626152469 25331864430897591850897)
                ·
                  rfl

theorem cell22_666004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 6].length) (baseStart_666004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666004 prefixEnd_666004 := by exact prefixLift 666004
  have htrace : WordTrace (prefixWord ++ tailWord_666004) baseStart_666004 baseEnd_666004 := by
    simpa [prefixWord, tailWord_666004, baseEnd_666004] using wordTrace_append hprefix tailTrace_666004
  have hstable : (prefixWord ++ tailWord_666004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666004).length < 2 ^ (prefixWord ++ tailWord_666004).sum := by decide
  have hdescent : baseEnd_666004 < baseStart_666004 := by decide
  rcases family_descends (prefixWord ++ tailWord_666004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666015 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 7]
def baseStart_666015 : Nat := 118140960795 + 666015 * 2 ^ 59
def prefixEnd_666015 : Nat := 4983230072969 + 3 ^ 40 * 666015 * 2
def baseEnd_666015 : Nat := 75996848467625988211013

theorem tailTrace_666015 : CollatzResearch.WordTrace tailWord_666015 prefixEnd_666015 75996848467625988211013 := by
  unfold tailWord_666015
  simp only [CollatzResearch.WordTrace]
  refine ⟨24291562682148876151303499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16194375121432584100868999 24291562682148876151303499)
  ·
    refine ⟨36437344023223314226955249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24291562682148876151303499 36437344023223314226955249)
    ·
      refine ⟨27328008017417485670216437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36437344023223314226955249 27328008017417485670216437)
      ·
        refine ⟨2562000751632889281582791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27328008017417485670216437 2562000751632889281582791)
        ·
          refine ⟨3843001127449333922374187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562000751632889281582791 3843001127449333922374187)
          ·
            refine ⟨5764501691174000883561281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843001127449333922374187 5764501691174000883561281)
            ·
              refine ⟨4323376268380500662670961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5764501691174000883561281 4323376268380500662670961)
              ·
                refine ⟨3242532201285375497003221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4323376268380500662670961 3242532201285375497003221)
                ·
                  refine ⟨75996848467625988211013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3242532201285375497003221 75996848467625988211013)
                  ·
                    rfl

theorem cell22_666015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 7].length) (baseStart_666015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666015 prefixEnd_666015 := by exact prefixLift 666015
  have htrace : WordTrace (prefixWord ++ tailWord_666015) baseStart_666015 baseEnd_666015 := by
    simpa [prefixWord, tailWord_666015, baseEnd_666015] using wordTrace_append hprefix tailTrace_666015
  have hstable : (prefixWord ++ tailWord_666015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666015).length < 2 ^ (prefixWord ++ tailWord_666015).sum := by decide
  have hdescent : baseEnd_666015 < baseStart_666015 := by decide
  rcases family_descends (prefixWord ++ tailWord_666015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666019 : List Nat := [1, 1, 1, 4, 1, 4, 1, 5, 1, 3]
def baseStart_666019 : Nat := 118140960795 + 666019 * 2 ^ 59
def prefixEnd_666019 : Nat := 4983230072969 + 3 ^ 40 * 666019 * 2
def baseEnd_666019 : Nat := 227991914684623287533027

theorem tailTrace_666019 : CollatzResearch.WordTrace tailWord_666019 prefixEnd_666019 227991914684623287533027 := by
  unfold tailWord_666019
  simp only [CollatzResearch.WordTrace]
  refine ⟨24291708574134384834449111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16194472382756256556299407 24291708574134384834449111)
  ·
    refine ⟨36437562861201577251673667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24291708574134384834449111 36437562861201577251673667)
    ·
      refine ⟨54656344291802365877510501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36437562861201577251673667 54656344291802365877510501)
      ·
        refine ⟨10248064554712943602033219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54656344291802365877510501 10248064554712943602033219)
        ·
          refine ⟨15372096832069415403049829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10248064554712943602033219 15372096832069415403049829)
          ·
            refine ⟨2882268156013015388071843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15372096832069415403049829 2882268156013015388071843)
            ·
              refine ⟨4323402234019523082107765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882268156013015388071843 4323402234019523082107765)
              ·
                refine ⟨405318959439330288947603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4323402234019523082107765 405318959439330288947603)
                ·
                  refine ⟨607978439158995433421405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405318959439330288947603 607978439158995433421405)
                  ·
                    refine ⟨227991914684623287533027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 607978439158995433421405 227991914684623287533027)
                    ·
                      rfl

theorem cell22_666019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 3].length) (baseStart_666019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666019 prefixEnd_666019 := by exact prefixLift 666019
  have htrace : WordTrace (prefixWord ++ tailWord_666019) baseStart_666019 baseEnd_666019 := by
    simpa [prefixWord, tailWord_666019, baseEnd_666019] using wordTrace_append hprefix tailTrace_666019
  have hstable : (prefixWord ++ tailWord_666019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666019).length < 2 ^ (prefixWord ++ tailWord_666019).sum := by decide
  have hdescent : baseEnd_666019 < baseStart_666019 := by decide
  rcases family_descends (prefixWord ++ tailWord_666019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666092 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_666092 : Nat := 118140960795 + 666092 * 2 ^ 59
def prefixEnd_666092 : Nat := 4983230072969 + 3 ^ 40 * 666092 * 2
def baseEnd_666092 : Nat := 228016904076475430457803

theorem tailTrace_666092 : CollatzResearch.WordTrace tailWord_666092 prefixEnd_666092 228016904076475430457803 := by
  unfold tailWord_666092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12147185551434959150928265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16196247401913278867904353 12147185551434959150928265)
  ·
    refine ⟨9110389163576219363196199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12147185551434959150928265 9110389163576219363196199)
    ·
      refine ⟨13665583745364329044794299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9110389163576219363196199 13665583745364329044794299)
      ·
        refine ⟨20498375618046493567191449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13665583745364329044794299 20498375618046493567191449)
        ·
          refine ⟨15373781713534870175393587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20498375618046493567191449 15373781713534870175393587)
          ·
            refine ⟨23060672570302305263090381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15373781713534870175393587 23060672570302305263090381)
            ·
              refine ⟨8647752213863364473658893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23060672570302305263090381 8647752213863364473658893)
              ·
                refine ⟨3242907080198761677622085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8647752213863364473658893 3242907080198761677622085)
                ·
                  refine ⟨608045077537267814554141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3242907080198761677622085 608045077537267814554141)
                  ·
                    refine ⟨228016904076475430457803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 608045077537267814554141 228016904076475430457803)
                    ·
                      rfl

theorem cell22_666092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_666092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666092 prefixEnd_666092 := by exact prefixLift 666092
  have htrace : WordTrace (prefixWord ++ tailWord_666092) baseStart_666092 baseEnd_666092 := by
    simpa [prefixWord, tailWord_666092, baseEnd_666092] using wordTrace_append hprefix tailTrace_666092
  have hstable : (prefixWord ++ tailWord_666092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666092).length < 2 ^ (prefixWord ++ tailWord_666092).sum := by decide
  have hdescent : baseEnd_666092 < baseStart_666092 := by decide
  rcases family_descends (prefixWord ++ tailWord_666092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666094 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_666094 : Nat := 118140960795 + 666094 * 2 ^ 59
def prefixEnd_666094 : Nat := 4983230072969 + 3 ^ 40 * 666094 * 2
def baseEnd_666094 : Nat := 76005862905782697302599

theorem tailTrace_666094 : CollatzResearch.WordTrace tailWord_666094 prefixEnd_666094 76005862905782697302599 := by
  unfold tailWord_666094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036805506107834080428667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16196296032575115095619557 3036805506107834080428667)
  ·
    refine ⟨4555208259161751120643001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3036805506107834080428667 4555208259161751120643001)
    ·
      refine ⟨3416406194371313340482251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4555208259161751120643001 3416406194371313340482251)
      ·
        refine ⟨5124609291556970010723377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416406194371313340482251 5124609291556970010723377)
        ·
          refine ⟨3843456968667727508042533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5124609291556970010723377 3843456968667727508042533)
          ·
            refine ⟨720648181625198907757975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3843456968667727508042533 720648181625198907757975)
            ·
              refine ⟨1080972272437798361636963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720648181625198907757975 1080972272437798361636963)
              ·
                refine ⟨1621458408656697542455445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080972272437798361636963 1621458408656697542455445)
                ·
                  refine ⟨76005862905782697302599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1621458408656697542455445 76005862905782697302599)
                  ·
                    rfl

theorem cell22_666094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_666094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666094 prefixEnd_666094 := by exact prefixLift 666094
  have htrace : WordTrace (prefixWord ++ tailWord_666094) baseStart_666094 baseEnd_666094 := by
    simpa [prefixWord, tailWord_666094, baseEnd_666094] using wordTrace_append hprefix tailTrace_666094
  have hstable : (prefixWord ++ tailWord_666094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666094).length < 2 ^ (prefixWord ++ tailWord_666094).sum := by decide
  have hdescent : baseEnd_666094 < baseStart_666094 := by decide
  rcases family_descends (prefixWord ++ tailWord_666094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666105 : List Nat := [1, 2, 1, 3, 1, 2, 3, 9]
def baseStart_666105 : Nat := 118140960795 + 666105 * 2 ^ 59
def prefixEnd_666105 : Nat := 4983230072969 + 3 ^ 40 * 666105 * 2
def baseEnd_666105 : Nat := 25335706026905303320307

theorem tailTrace_666105 : CollatzResearch.WordTrace tailWord_666105 prefixEnd_666105 25335706026905303320307 := by
  unfold tailWord_666105
  simp only [CollatzResearch.WordTrace]
  refine ⟨24294845251822821522079769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16196563501215214348053179 24294845251822821522079769)
  ·
    refine ⟨18221133938867116141559827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24294845251822821522079769 18221133938867116141559827)
    ·
      refine ⟨27331700908300674212339741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18221133938867116141559827 27331700908300674212339741)
      ·
        refine ⟨10249387840612752829627403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27331700908300674212339741 10249387840612752829627403)
        ·
          refine ⟨15374081760919129244441105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10249387840612752829627403 15374081760919129244441105)
          ·
            refine ⟨11530561320689346933330829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15374081760919129244441105 11530561320689346933330829)
            ·
              refine ⟨4323960495258505099999061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11530561320689346933330829 4323960495258505099999061)
              ·
                refine ⟨25335706026905303320307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4323960495258505099999061 25335706026905303320307)
                ·
                  rfl

theorem cell22_666105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 9].length) (baseStart_666105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666105 prefixEnd_666105 := by exact prefixLift 666105
  have htrace : WordTrace (prefixWord ++ tailWord_666105) baseStart_666105 baseEnd_666105 := by
    simpa [prefixWord, tailWord_666105, baseEnd_666105] using wordTrace_append hprefix tailTrace_666105
  have hstable : (prefixWord ++ tailWord_666105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666105).length < 2 ^ (prefixWord ++ tailWord_666105).sum := by decide
  have hdescent : baseEnd_666105 < baseStart_666105 := by decide
  rcases family_descends (prefixWord ++ tailWord_666105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666109 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_666109 : Nat := 118140960795 + 666109 * 2 ^ 59
def prefixEnd_666109 : Nat := 4983230072969 + 3 ^ 40 * 666109 * 2
def baseEnd_666109 : Nat := 228022723523893052782751

theorem tailTrace_666109 : CollatzResearch.WordTrace tailWord_666109 prefixEnd_666109 228022723523893052782751 := by
  unfold tailWord_666109
  simp only [CollatzResearch.WordTrace]
  refine ⟨24294991143808330205225381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16196660762538886803483587 24294991143808330205225381)
  ·
    refine ⟨4555310839464061913479759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24294991143808330205225381 4555310839464061913479759)
    ·
      refine ⟨6832966259196092870219639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4555310839464061913479759 6832966259196092870219639)
      ·
        refine ⟨10249449388794139305329459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6832966259196092870219639 10249449388794139305329459)
        ·
          refine ⟨15374174083191208957994189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10249449388794139305329459 15374174083191208957994189)
          ·
            refine ⟨5765315281196703359247821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15374174083191208957994189 5765315281196703359247821)
            ·
              refine ⟨2161993230448763759717933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5765315281196703359247821 2161993230448763759717933)
              ·
                refine ⟨810747461418286409894225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2161993230448763759717933 810747461418286409894225)
                ·
                  refine ⟨608060596063714807420669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 810747461418286409894225 608060596063714807420669)
                  ·
                    refine ⟨228022723523893052782751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 608060596063714807420669 228022723523893052782751)
                    ·
                      rfl

theorem cell22_666109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_666109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666109 prefixEnd_666109 := by exact prefixLift 666109
  have htrace : WordTrace (prefixWord ++ tailWord_666109) baseStart_666109 baseEnd_666109 := by
    simpa [prefixWord, tailWord_666109, baseEnd_666109] using wordTrace_append hprefix tailTrace_666109
  have hstable : (prefixWord ++ tailWord_666109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666109).length < 2 ^ (prefixWord ++ tailWord_666109).sum := by decide
  have hdescent : baseEnd_666109 < baseStart_666109 := by decide
  rcases family_descends (prefixWord ++ tailWord_666109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666124 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_666124 : Nat := 118140960795 + 666124 * 2 ^ 59
def prefixEnd_666124 : Nat := 4983230072969 + 3 ^ 40 * 666124 * 2
def baseEnd_666124 : Nat := 228027858330438013657705

theorem tailTrace_666124 : CollatzResearch.WordTrace tailWord_666124 prefixEnd_666124 228027858330438013657705 := by
  unfold tailWord_666124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12147769119376993883510713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16197025492502658511347617 12147769119376993883510713)
  ·
    refine ⟨9110826839532745412633035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12147769119376993883510713 9110826839532745412633035)
    ·
      refine ⟨13666240259299118118949553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9110826839532745412633035 13666240259299118118949553)
      ·
        refine ⟨10249680194474338589212165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13666240259299118118949553 10249680194474338589212165)
        ·
          refine ⟨1921815036463938485477281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10249680194474338589212165 1921815036463938485477281)
          ·
            refine ⟨1441361277347953864107961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1921815036463938485477281 1441361277347953864107961)
            ·
              refine ⟨1081020958010965398080971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441361277347953864107961 1081020958010965398080971)
              ·
                refine ⟨1621531437016448097121457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081020958010965398080971 1621531437016448097121457)
                ·
                  refine ⟨1216148577762336072841093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1621531437016448097121457 1216148577762336072841093)
                  ·
                    refine ⟨228027858330438013657705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216148577762336072841093 228027858330438013657705)
                    ·
                      rfl

theorem cell22_666124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_666124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666124 prefixEnd_666124 := by exact prefixLift 666124
  have htrace : WordTrace (prefixWord ++ tailWord_666124) baseStart_666124 baseEnd_666124 := by
    simpa [prefixWord, tailWord_666124, baseEnd_666124] using wordTrace_append hprefix tailTrace_666124
  have hstable : (prefixWord ++ tailWord_666124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666124).length < 2 ^ (prefixWord ++ tailWord_666124).sum := by decide
  have hdescent : baseEnd_666124 < baseStart_666124 := by decide
  rcases family_descends (prefixWord ++ tailWord_666124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666137 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 5, 3]
def baseStart_666137 : Nat := 118140960795 + 666137 * 2 ^ 59
def prefixEnd_666137 : Nat := 4983230072969 + 3 ^ 40 * 666137 * 2
def baseEnd_666137 : Nat := 228032308496110313082665

theorem tailTrace_666137 : CollatzResearch.WordTrace tailWord_666137 prefixEnd_666137 228032308496110313082665 := by
  unfold tailWord_666137
  simp only [CollatzResearch.WordTrace]
  refine ⟨24296012387706890987244665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16197341591804593991496443 24296012387706890987244665)
  ·
    refine ⟨18222009290780168240433499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24296012387706890987244665 18222009290780168240433499)
    ·
      refine ⟨27333013936170252360650249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18222009290780168240433499 27333013936170252360650249)
      ·
        refine ⟨20499760452127689270487687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27333013936170252360650249 20499760452127689270487687)
        ·
          refine ⟨30749640678191533905731531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20499760452127689270487687 30749640678191533905731531)
          ·
            refine ⟨46124461017287300858597297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30749640678191533905731531 46124461017287300858597297)
            ·
              refine ⟨34593345762965475643947973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46124461017287300858597297 34593345762965475643947973)
              ·
                refine ⟨6486252330556026683240245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34593345762965475643947973 6486252330556026683240245)
                ·
                  refine ⟨608086155989627501553773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6486252330556026683240245 608086155989627501553773)
                  ·
                    refine ⟨228032308496110313082665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 608086155989627501553773 228032308496110313082665)
                    ·
                      rfl

theorem cell22_666137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_666137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666137 prefixEnd_666137 := by exact prefixLift 666137
  have htrace : WordTrace (prefixWord ++ tailWord_666137) baseStart_666137 baseEnd_666137 := by
    simpa [prefixWord, tailWord_666137, baseEnd_666137] using wordTrace_append hprefix tailTrace_666137
  have hstable : (prefixWord ++ tailWord_666137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666137).length < 2 ^ (prefixWord ++ tailWord_666137).sum := by decide
  have hdescent : baseEnd_666137 < baseStart_666137 := by decide
  rcases family_descends (prefixWord ++ tailWord_666137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666167 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 5]
def baseStart_666167 : Nat := 118140960795 + 666167 * 2 ^ 59
def prefixEnd_666167 : Nat := 4983230072969 + 3 ^ 40 * 666167 * 2
def baseEnd_666167 : Nat := 76014192703066744944191

theorem tailTrace_666167 : CollatzResearch.WordTrace tailWord_666167 prefixEnd_666167 76014192703066744944191 := by
  unfold tailWord_666167
  simp only [CollatzResearch.WordTrace]
  refine ⟨24297106577598206110836755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16198071051732137407224503 24297106577598206110836755)
  ·
    refine ⟨36445659866397309166255133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24297106577598206110836755 36445659866397309166255133)
    ·
      refine ⟨13667122449898990937345675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36445659866397309166255133 13667122449898990937345675)
      ·
        refine ⟨20500683674848486406018513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13667122449898990937345675 20500683674848486406018513)
        ·
          refine ⟨15375512756136364804513885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20500683674848486406018513 15375512756136364804513885)
          ·
            refine ⟨5765817283551136801692707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15375512756136364804513885 5765817283551136801692707)
            ·
              refine ⟨8648725925326705202539061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765817283551136801692707 8648725925326705202539061)
              ·
                refine ⟨810818055499378612738037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8648725925326705202539061 810818055499378612738037)
                ·
                  refine ⟨76014192703066744944191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810818055499378612738037 76014192703066744944191)
                  ·
                    rfl

theorem cell22_666167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 5].length) (baseStart_666167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666167 prefixEnd_666167 := by exact prefixLift 666167
  have htrace : WordTrace (prefixWord ++ tailWord_666167) baseStart_666167 baseEnd_666167 := by
    simpa [prefixWord, tailWord_666167, baseEnd_666167] using wordTrace_append hprefix tailTrace_666167
  have hstable : (prefixWord ++ tailWord_666167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666167).length < 2 ^ (prefixWord ++ tailWord_666167).sum := by decide
  have hdescent : baseEnd_666167 < baseStart_666167 := by decide
  rcases family_descends (prefixWord ++ tailWord_666167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666227 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 1, 5]
def baseStart_666227 : Nat := 118140960795 + 666227 * 2 ^ 59
def prefixEnd_666227 : Nat := 4983230072969 + 3 ^ 40 * 666227 * 2
def baseEnd_666227 : Nat := 228063117335380078332389

theorem tailTrace_666227 : CollatzResearch.WordTrace tailWord_666227 prefixEnd_666227 228063117335380078332389 := by
  unfold tailWord_666227
  simp only [CollatzResearch.WordTrace]
  refine ⟨24299294957380836358020935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16199529971587224238680623 24299294957380836358020935)
  ·
    refine ⟨36448942436071254537031403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24299294957380836358020935 36448942436071254537031403)
    ·
      refine ⟨54673413654106881805547105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36448942436071254537031403 54673413654106881805547105)
      ·
        refine ⟨41005060240580161354160329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54673413654106881805547105 41005060240580161354160329)
        ·
          refine ⟨30753795180435121015620247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41005060240580161354160329 30753795180435121015620247)
          ·
            refine ⟨46130692770652681523430371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30753795180435121015620247 46130692770652681523430371)
            ·
              refine ⟨69196039155979022285145557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46130692770652681523430371 69196039155979022285145557)
              ·
                refine ⟨1621782167718258334808099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 69196039155979022285145557 1621782167718258334808099)
                ·
                  refine ⟨2432673251577387502212149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621782167718258334808099 2432673251577387502212149)
                  ·
                    refine ⟨228063117335380078332389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2432673251577387502212149 228063117335380078332389)
                    ·
                      rfl

theorem cell22_666227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_666227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666227 prefixEnd_666227 := by exact prefixLift 666227
  have htrace : WordTrace (prefixWord ++ tailWord_666227) baseStart_666227 baseEnd_666227 := by
    simpa [prefixWord, tailWord_666227, baseEnd_666227] using wordTrace_append hprefix tailTrace_666227
  have hstable : (prefixWord ++ tailWord_666227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666227).length < 2 ^ (prefixWord ++ tailWord_666227).sum := by decide
  have hdescent : baseEnd_666227 < baseStart_666227 := by decide
  rcases family_descends (prefixWord ++ tailWord_666227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666282 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_666282 : Nat := 118140960795 + 666282 * 2 ^ 59
def prefixEnd_666282 : Nat := 4983230072969 + 3 ^ 40 * 666282 * 2
def baseEnd_666282 : Nat := 228081944959378268207221

theorem tailTrace_666282 : CollatzResearch.WordTrace tailWord_666282 prefixEnd_666282 228081944959378268207221 := by
  unfold tailWord_666282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075325243045395187818275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16200867314787720500848733 6075325243045395187818275)
  ·
    refine ⟨9112987864568092781727413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6075325243045395187818275 9112987864568092781727413)
    ·
      refine ⟨854342612303258698286945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9112987864568092781727413 854342612303258698286945)
      ·
        refine ⟨640756959227444023715209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 854342612303258698286945 640756959227444023715209)
        ·
          refine ⟨480567719420583017786407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 640756959227444023715209 480567719420583017786407)
          ·
            refine ⟨720851579130874526679611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480567719420583017786407 720851579130874526679611)
            ·
              refine ⟨1081277368696311790019417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720851579130874526679611 1081277368696311790019417)
              ·
                refine ⟨810958026522233842514563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081277368696311790019417 810958026522233842514563)
                ·
                  refine ⟨1216437039783350763771845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810958026522233842514563 1216437039783350763771845)
                  ·
                    refine ⟨228081944959378268207221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216437039783350763771845 228081944959378268207221)
                    ·
                      rfl

theorem cell22_666282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_666282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666282 prefixEnd_666282 := by exact prefixLift 666282
  have htrace : WordTrace (prefixWord ++ tailWord_666282) baseStart_666282 baseEnd_666282 := by
    simpa [prefixWord, tailWord_666282, baseEnd_666282] using wordTrace_append hprefix tailTrace_666282
  have hstable : (prefixWord ++ tailWord_666282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666282).length < 2 ^ (prefixWord ++ tailWord_666282).sum := by decide
  have hdescent : baseEnd_666282 < baseStart_666282 := by decide
  rcases family_descends (prefixWord ++ tailWord_666282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666394 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_666394 : Nat := 118140960795 + 666394 * 2 ^ 59
def prefixEnd_666394 : Nat := 4983230072969 + 3 ^ 40 * 666394 * 2
def baseEnd_666394 : Nat := 228120284848247309406877

theorem tailTrace_666394 : CollatzResearch.WordTrace tailWord_666394 prefixEnd_666394 228120284848247309406877 := by
  unfold tailWord_666394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6076346486943955969837559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16203590631850549252900157 6076346486943955969837559)
  ·
    refine ⟨9114519730415933954756339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6076346486943955969837559 9114519730415933954756339)
    ·
      refine ⟨13671779595623900932134509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114519730415933954756339 13671779595623900932134509)
      ·
        refine ⟨5126917348358962849550441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13671779595623900932134509 5126917348358962849550441)
        ·
          refine ⟨3845188011269222137162831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5126917348358962849550441 3845188011269222137162831)
          ·
            refine ⟨5767782016903833205744247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845188011269222137162831 5767782016903833205744247)
            ·
              refine ⟨8651673025355749808616371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767782016903833205744247 8651673025355749808616371)
              ·
                refine ⟨12977509538033624712924557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651673025355749808616371 12977509538033624712924557)
                ·
                  refine ⟨4866566076762609267346709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12977509538033624712924557 4866566076762609267346709)
                  ·
                    refine ⟨228120284848247309406877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4866566076762609267346709 228120284848247309406877)
                    ·
                      rfl

theorem cell22_666394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_666394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666394 prefixEnd_666394 := by exact prefixLift 666394
  have htrace : WordTrace (prefixWord ++ tailWord_666394) baseStart_666394 baseEnd_666394 := by
    simpa [prefixWord, tailWord_666394, baseEnd_666394] using wordTrace_append hprefix tailTrace_666394
  have hstable : (prefixWord ++ tailWord_666394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666394).length < 2 ^ (prefixWord ++ tailWord_666394).sum := by decide
  have hdescent : baseEnd_666394 < baseStart_666394 := by decide
  rcases family_descends (prefixWord ++ tailWord_666394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666396 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_666396 : Nat := 118140960795 + 666396 * 2 ^ 59
def prefixEnd_666396 : Nat := 4983230072969 + 3 ^ 40 * 666396 * 2
def baseEnd_666396 : Nat := 228120969489119970856871

theorem tailTrace_666396 : CollatzResearch.WordTrace tailWord_666396 prefixEnd_666396 228120969489119970856871 := by
  unfold tailWord_666396
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152729446884289110461521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16203639262512385480615361 12152729446884289110461521)
  ·
    refine ⟨9114547085163216832846141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12152729446884289110461521 9114547085163216832846141)
    ·
      refine ⟨3417955156936206312317303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9114547085163216832846141 3417955156936206312317303)
      ·
        refine ⟨5126932735404309468475955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3417955156936206312317303 5126932735404309468475955)
        ·
          refine ⟨7690399103106464202713933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5126932735404309468475955 7690399103106464202713933)
          ·
            refine ⟨2883899663664924076017725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7690399103106464202713933 2883899663664924076017725)
            ·
              refine ⟨1081462373874346528506647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2883899663664924076017725 1081462373874346528506647)
              ·
                refine ⟨1622193560811519792759971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081462373874346528506647 1622193560811519792759971)
                ·
                  refine ⟨2433290341217279689139957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622193560811519792759971 2433290341217279689139957)
                  ·
                    refine ⟨228120969489119970856871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2433290341217279689139957 228120969489119970856871)
                    ·
                      rfl

theorem cell22_666396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_666396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666396 prefixEnd_666396 := by exact prefixLift 666396
  have htrace : WordTrace (prefixWord ++ tailWord_666396) baseStart_666396 baseEnd_666396 := by
    simpa [prefixWord, tailWord_666396, baseEnd_666396] using wordTrace_append hprefix tailTrace_666396
  have hstable : (prefixWord ++ tailWord_666396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666396).length < 2 ^ (prefixWord ++ tailWord_666396).sum := by decide
  have hdescent : baseEnd_666396 < baseStart_666396 := by decide
  rcases family_descends (prefixWord ++ tailWord_666396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666426 : List Nat := [3, 1, 1, 1, 6, 2, 8]
def baseStart_666426 : Nat := 118140960795 + 666426 * 2 ^ 59
def prefixEnd_666426 : Nat := 4983230072969 + 3 ^ 40 * 666426 * 2
def baseEnd_666426 : Nat := 8449305151933699726177

theorem tailTrace_666426 : CollatzResearch.WordTrace tailWord_666426 prefixEnd_666426 8449305151933699726177 := by
  unfold tailWord_666426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6076638270914973336128783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16204368722439928896343421 6076638270914973336128783)
  ·
    refine ⟨9114957406372460004193175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6076638270914973336128783 9114957406372460004193175)
    ·
      refine ⟨13672436109558690006289763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114957406372460004193175 13672436109558690006289763)
      ·
        refine ⟨20508654164338035009434645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13672436109558690006289763 20508654164338035009434645)
        ·
          refine ⟨961343163953345391067249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20508654164338035009434645 961343163953345391067249)
          ·
            refine ⟨721007372965009043300437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 961343163953345391067249 721007372965009043300437)
            ·
              refine ⟨8449305151933699726177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 721007372965009043300437 8449305151933699726177)
              ·
                rfl

theorem cell22_666426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 8].length) (baseStart_666426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666426 prefixEnd_666426 := by exact prefixLift 666426
  have htrace : WordTrace (prefixWord ++ tailWord_666426) baseStart_666426 baseEnd_666426 := by
    simpa [prefixWord, tailWord_666426, baseEnd_666426] using wordTrace_append hprefix tailTrace_666426
  have hstable : (prefixWord ++ tailWord_666426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666426).length < 2 ^ (prefixWord ++ tailWord_666426).sum := by decide
  have hdescent : baseEnd_666426 < baseStart_666426 := by decide
  rcases family_descends (prefixWord ++ tailWord_666426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666439 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 2, 6]
def baseStart_666439 : Nat := 118140960795 + 666439 * 2 ^ 59
def prefixEnd_666439 : Nat := 4983230072969 + 3 ^ 40 * 666439 * 2
def baseEnd_666439 : Nat := 228135689267882192031739

theorem tailTrace_666439 : CollatzResearch.WordTrace tailWord_666439 prefixEnd_666439 228135689267882192031739 := by
  unfold tailWord_666439
  simp only [CollatzResearch.WordTrace]
  refine ⟨24307027232612796564738371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16204684821741864376492247 24307027232612796564738371)
  ·
    refine ⟨36460540848919194847107557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24307027232612796564738371 36460540848919194847107557)
    ·
      refine ⟨6836351409172349033832667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36460540848919194847107557 6836351409172349033832667)
      ·
        refine ⟨10254527113758523550749001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6836351409172349033832667 10254527113758523550749001)
        ·
          refine ⟨7690895335318892663061751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10254527113758523550749001 7690895335318892663061751)
          ·
            refine ⟨11536343002978338994592627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7690895335318892663061751 11536343002978338994592627)
            ·
              refine ⟨17304514504467508491888941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11536343002978338994592627 17304514504467508491888941)
              ·
                refine ⟨6489192939175315684458353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17304514504467508491888941 6489192939175315684458353)
                ·
                  refine ⟨4866894704381486763343765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6489192939175315684458353 4866894704381486763343765)
                  ·
                    refine ⟨228135689267882192031739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4866894704381486763343765 228135689267882192031739)
                    ·
                      rfl

theorem cell22_666439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_666439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666439 prefixEnd_666439 := by exact prefixLift 666439
  have htrace : WordTrace (prefixWord ++ tailWord_666439) baseStart_666439 baseEnd_666439 := by
    simpa [prefixWord, tailWord_666439, baseEnd_666439] using wordTrace_append hprefix tailTrace_666439
  have hstable : (prefixWord ++ tailWord_666439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666439).length < 2 ^ (prefixWord ++ tailWord_666439).sum := by decide
  have hdescent : baseEnd_666439 < baseStart_666439 := by decide
  rcases family_descends (prefixWord ++ tailWord_666439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666501 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_666501 : Nat := 118140960795 + 666501 * 2 ^ 59
def prefixEnd_666501 : Nat := 4983230072969 + 3 ^ 40 * 666501 * 2
def baseEnd_666501 : Nat := 228156913134934696981549

theorem tailTrace_666501 : CollatzResearch.WordTrace tailWord_666501 prefixEnd_666501 228156913134934696981549 := by
  unfold tailWord_666501
  simp only [CollatzResearch.WordTrace]
  refine ⟨24309288558388181153495357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16206192372258787435663571 24309288558388181153495357)
  ·
    refine ⟨9115983209395567932560759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24309288558388181153495357 9115983209395567932560759)
    ·
      refine ⟨13673974814093351898841139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9115983209395567932560759 13673974814093351898841139)
      ·
        refine ⟨20510962221140027848261709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13673974814093351898841139 20510962221140027848261709)
        ·
          refine ⟨7691610832927510443098141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20510962221140027848261709 7691610832927510443098141)
          ·
            refine ⟨2884354062347816416161803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7691610832927510443098141 2884354062347816416161803)
            ·
              refine ⟨4326531093521724624242705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2884354062347816416161803 4326531093521724624242705)
              ·
                refine ⟨3244898320141293468182029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326531093521724624242705 3244898320141293468182029)
                ·
                  refine ⟨1216836870052985050568261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3244898320141293468182029 1216836870052985050568261)
                  ·
                    refine ⟨228156913134934696981549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216836870052985050568261 228156913134934696981549)
                    ·
                      rfl

theorem cell22_666501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_666501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666501 prefixEnd_666501 := by exact prefixLift 666501
  have htrace : WordTrace (prefixWord ++ tailWord_666501) baseStart_666501 baseEnd_666501 := by
    simpa [prefixWord, tailWord_666501, baseEnd_666501] using wordTrace_append hprefix tailTrace_666501
  have hstable : (prefixWord ++ tailWord_666501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666501).length < 2 ^ (prefixWord ++ tailWord_666501).sum := by decide
  have hdescent : baseEnd_666501 < baseStart_666501 := by decide
  rcases family_descends (prefixWord ++ tailWord_666501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666531 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 1, 5]
def baseStart_666531 : Nat := 118140960795 + 666531 * 2 ^ 59
def prefixEnd_666531 : Nat := 4983230072969 + 3 ^ 40 * 666531 * 2
def baseEnd_666531 : Nat := 228167182748024618731457

theorem tailTrace_666531 : CollatzResearch.WordTrace tailWord_666531 prefixEnd_666531 228167182748024618731457 := by
  unfold tailWord_666531
  simp only [CollatzResearch.WordTrace]
  refine ⟨24310382748279496277087447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16206921832186330851391631 24310382748279496277087447)
  ·
    refine ⟨36465574122419244415631171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24310382748279496277087447 36465574122419244415631171)
    ·
      refine ⟨54698361183628866623446757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36465574122419244415631171 54698361183628866623446757)
      ·
        refine ⟨10255942721930412491896267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54698361183628866623446757 10255942721930412491896267)
        ·
          refine ⟨15383914082895618737844401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10255942721930412491896267 15383914082895618737844401)
          ·
            refine ⟨11537935562171714053383301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15383914082895618737844401 11537935562171714053383301)
            ·
              refine ⟨2163362917907196385009369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11537935562171714053383301 2163362917907196385009369)
              ·
                refine ⟨1622522188430397288757027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163362917907196385009369 1622522188430397288757027)
                ·
                  refine ⟨2433783282645595933135541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622522188430397288757027 2433783282645595933135541)
                  ·
                    refine ⟨228167182748024618731457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2433783282645595933135541 228167182748024618731457)
                    ·
                      rfl

theorem cell22_666531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_666531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666531 prefixEnd_666531 := by exact prefixLift 666531
  have htrace : WordTrace (prefixWord ++ tailWord_666531) baseStart_666531 baseEnd_666531 := by
    simpa [prefixWord, tailWord_666531, baseEnd_666531] using wordTrace_append hprefix tailTrace_666531
  have hstable : (prefixWord ++ tailWord_666531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666531).length < 2 ^ (prefixWord ++ tailWord_666531).sum := by decide
  have hdescent : baseEnd_666531 < baseStart_666531 := by decide
  rcases family_descends (prefixWord ++ tailWord_666531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666535 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 1, 4]
def baseStart_666535 : Nat := 118140960795 + 666535 * 2 ^ 59
def prefixEnd_666535 : Nat := 4983230072969 + 3 ^ 40 * 666535 * 2
def baseEnd_666535 : Nat := 228168552029769941631445

theorem tailTrace_666535 : CollatzResearch.WordTrace tailWord_666535 prefixEnd_666535 228168552029769941631445 := by
  unfold tailWord_666535
  simp only [CollatzResearch.WordTrace]
  refine ⟨24310528640265004960233059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16207019093510003306822039 24310528640265004960233059)
  ·
    refine ⟨36465792960397507440349589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24310528640265004960233059 36465792960397507440349589)
    ·
      refine ⟨1709334045018633161266387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36465792960397507440349589 1709334045018633161266387)
      ·
        refine ⟨2564001067527949741899581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709334045018633161266387 2564001067527949741899581)
        ·
          refine ⟨961500400322981153212343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2564001067527949741899581 961500400322981153212343)
          ·
            refine ⟨1442250600484471729818515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961500400322981153212343 1442250600484471729818515)
            ·
              refine ⟨2163375900726707594727773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442250600484471729818515 2163375900726707594727773)
              ·
                refine ⟨811265962772515348022915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2163375900726707594727773 811265962772515348022915)
                ·
                  refine ⟨1216898944158773022034373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811265962772515348022915 1216898944158773022034373)
                  ·
                    refine ⟨228168552029769941631445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1216898944158773022034373 228168552029769941631445)
                    ·
                      rfl

theorem cell22_666535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_666535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666535 prefixEnd_666535 := by exact prefixLift 666535
  have htrace : WordTrace (prefixWord ++ tailWord_666535) baseStart_666535 baseEnd_666535 := by
    simpa [prefixWord, tailWord_666535, baseEnd_666535] using wordTrace_append hprefix tailTrace_666535
  have hstable : (prefixWord ++ tailWord_666535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666535).length < 2 ^ (prefixWord ++ tailWord_666535).sum := by decide
  have hdescent : baseEnd_666535 < baseStart_666535 := by decide
  rcases family_descends (prefixWord ++ tailWord_666535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666578 : List Nat := [3, 2, 2, 3, 1, 2, 1, 8]
def baseStart_666578 : Nat := 118140960795 + 666578 * 2 ^ 59
def prefixEnd_666578 : Nat := 4983230072969 + 3 ^ 40 * 666578 * 2
def baseEnd_666578 : Nat := 25353696867614684756257

theorem tailTrace_666578 : CollatzResearch.WordTrace tailWord_666578 prefixEnd_666578 25353696867614684756257 := by
  unfold tailWord_666578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078024244777305826012097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16208064652739482202698925 6078024244777305826012097)
  ·
    refine ⟨4558518183582979369509073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6078024244777305826012097 4558518183582979369509073)
    ·
      refine ⟨3418888637687234527131805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4558518183582979369509073 3418888637687234527131805)
      ·
        refine ⟨1282083239132712947674427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3418888637687234527131805 1282083239132712947674427)
        ·
          refine ⟨1923124858699069421511641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282083239132712947674427 1923124858699069421511641)
          ·
            refine ⟨1442343644024302066133731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1923124858699069421511641 1442343644024302066133731)
            ·
              refine ⟨2163515466036453099200597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442343644024302066133731 2163515466036453099200597)
              ·
                refine ⟨25353696867614684756257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2163515466036453099200597 25353696867614684756257)
                ·
                  rfl

theorem cell22_666578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_666578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666578 prefixEnd_666578 := by exact prefixLift 666578
  have htrace : WordTrace (prefixWord ++ tailWord_666578) baseStart_666578 baseEnd_666578 := by
    simpa [prefixWord, tailWord_666578, baseEnd_666578] using wordTrace_append hprefix tailTrace_666578
  have hstable : (prefixWord ++ tailWord_666578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666578).length < 2 ^ (prefixWord ++ tailWord_666578).sum := by decide
  have hdescent : baseEnd_666578 < baseStart_666578 := by decide
  rcases family_descends (prefixWord ++ tailWord_666578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666621 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_666621 : Nat := 118140960795 + 666621 * 2 ^ 59
def prefixEnd_666621 : Nat := 4983230072969 + 3 ^ 40 * 666621 * 2
def baseEnd_666621 : Nat := 228197991587294383981181

theorem tailTrace_666621 : CollatzResearch.WordTrace tailWord_666621 prefixEnd_666621 228197991587294383981181 := by
  unfold tailWord_666621
  simp only [CollatzResearch.WordTrace]
  refine ⟨24313665317953441647863717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16209110211968961098575811 24313665317953441647863717)
  ·
    refine ⟨4558812247116270308974447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24313665317953441647863717 4558812247116270308974447)
    ·
      refine ⟨6838218370674405463461671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4558812247116270308974447 6838218370674405463461671)
      ·
        refine ⟨10257327556011608195192507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838218370674405463461671 10257327556011608195192507)
        ·
          refine ⟨15385991334017412292788761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10257327556011608195192507 15385991334017412292788761)
          ·
            refine ⟨11539493500513059219591571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15385991334017412292788761 11539493500513059219591571)
            ·
              refine ⟨17309240250769588829387357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11539493500513059219591571 17309240250769588829387357)
              ·
                refine ⟨6490965094038595811020259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17309240250769588829387357 6490965094038595811020259)
                ·
                  refine ⟨9736447641057893716530389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6490965094038595811020259 9736447641057893716530389)
                  ·
                    refine ⟨228197991587294383981181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9736447641057893716530389 228197991587294383981181)
                    ·
                      rfl

theorem cell22_666621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_666621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666621 prefixEnd_666621 := by exact prefixLift 666621
  have htrace : WordTrace (prefixWord ++ tailWord_666621) baseStart_666621 baseEnd_666621 := by
    simpa [prefixWord, tailWord_666621, baseEnd_666621] using wordTrace_append hprefix tailTrace_666621
  have hstable : (prefixWord ++ tailWord_666621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666621).length < 2 ^ (prefixWord ++ tailWord_666621).sum := by decide
  have hdescent : baseEnd_666621 < baseStart_666621 := by decide
  rcases family_descends (prefixWord ++ tailWord_666621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666734 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_666734 : Nat := 118140960795 + 666734 * 2 ^ 59
def prefixEnd_666734 : Nat := 4983230072969 + 3 ^ 40 * 666734 * 2
def baseEnd_666734 : Nat := 228236673796599755905835

theorem tailTrace_666734 : CollatzResearch.WordTrace tailWord_666734 prefixEnd_666734 228236673796599755905835 := by
  unfold tailWord_666734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039723345818007743340907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16211857844362707964484837 3039723345818007743340907)
  ·
    refine ⟨4559585018727011615011361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3039723345818007743340907 4559585018727011615011361)
    ·
      refine ⟨3419688764045258711258521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4559585018727011615011361 3419688764045258711258521)
      ·
        refine ⟨2564766573033944033443891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3419688764045258711258521 2564766573033944033443891)
        ·
          refine ⟨3847149859550916050165837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564766573033944033443891 3847149859550916050165837)
          ·
            refine ⟨1442681197331593518812189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3847149859550916050165837 1442681197331593518812189)
            ·
              refine ⟨541005448999347569554571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1442681197331593518812189 541005448999347569554571)
              ·
                refine ⟨811508173499021354331857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541005448999347569554571 811508173499021354331857)
                ·
                  refine ⟨608631130124266015748893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 811508173499021354331857 608631130124266015748893)
                  ·
                    refine ⟨228236673796599755905835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 608631130124266015748893 228236673796599755905835)
                    ·
                      rfl

theorem cell22_666734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_666734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666734 prefixEnd_666734 := by exact prefixLift 666734
  have htrace : WordTrace (prefixWord ++ tailWord_666734) baseStart_666734 baseEnd_666734 := by
    simpa [prefixWord, tailWord_666734, baseEnd_666734] using wordTrace_append hprefix tailTrace_666734
  have hstable : (prefixWord ++ tailWord_666734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666734).length < 2 ^ (prefixWord ++ tailWord_666734).sum := by decide
  have hdescent : baseEnd_666734 < baseStart_666734 := by decide
  rcases family_descends (prefixWord ++ tailWord_666734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666773 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_666773 : Nat := 118140960795 + 666773 * 2 ^ 59
def prefixEnd_666773 : Nat := 4983230072969 + 3 ^ 40 * 666773 * 2
def baseEnd_666773 : Nat := 228250024293616654180715

theorem tailTrace_666773 : CollatzResearch.WordTrace tailWord_666773 prefixEnd_666773 228250024293616654180715 := by
  unfold tailWord_666773
  simp only [CollatzResearch.WordTrace]
  refine ⟨24319209213402771607396973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16212806142268514404931315 24319209213402771607396973)
  ·
    refine ⟨9119703455026039352773865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24319209213402771607396973 9119703455026039352773865)
    ·
      refine ⟨6839777591269529514580399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9119703455026039352773865 6839777591269529514580399)
      ·
        refine ⟨10259666386904294271870599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839777591269529514580399 10259666386904294271870599)
        ·
          refine ⟨15389499580356441407805899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10259666386904294271870599 15389499580356441407805899)
          ·
            refine ⟨23084249370534662111708849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15389499580356441407805899 23084249370534662111708849)
            ·
              refine ⟨17313187027900996583781637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23084249370534662111708849 17313187027900996583781637)
              ·
                refine ⟨3246222567731436859459057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17313187027900996583781637 3246222567731436859459057)
                ·
                  refine ⟨2434666925798577644594293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3246222567731436859459057 2434666925798577644594293)
                  ·
                    refine ⟨228250024293616654180715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2434666925798577644594293 228250024293616654180715)
                    ·
                      rfl

theorem cell22_666773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_666773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666773 prefixEnd_666773 := by exact prefixLift 666773
  have htrace : WordTrace (prefixWord ++ tailWord_666773) baseStart_666773 baseEnd_666773 := by
    simpa [prefixWord, tailWord_666773, baseEnd_666773] using wordTrace_append hprefix tailTrace_666773
  have hstable : (prefixWord ++ tailWord_666773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666773).length < 2 ^ (prefixWord ++ tailWord_666773).sum := by decide
  have hdescent : baseEnd_666773 < baseStart_666773 := by decide
  rcases family_descends (prefixWord ++ tailWord_666773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666803 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 6]
def baseStart_666803 : Nat := 118140960795 + 666803 * 2 ^ 59
def prefixEnd_666803 : Nat := 4983230072969 + 3 ^ 40 * 666803 * 2
def baseEnd_666803 : Nat := 76086764635568858643541

theorem tailTrace_666803 : CollatzResearch.WordTrace tailWord_666803 prefixEnd_666803 76086764635568858643541 := by
  unfold tailWord_666803
  simp only [CollatzResearch.WordTrace]
  refine ⟨24320303403294086730989063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16213535602196057820659375 24320303403294086730989063)
  ·
    refine ⟨36480455104941130096483595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24320303403294086730989063 36480455104941130096483595)
    ·
      refine ⟨54720682657411695144725393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36480455104941130096483595 54720682657411695144725393)
      ·
        refine ⟨41040511993058771358544045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54720682657411695144725393 41040511993058771358544045)
        ·
          refine ⟨15390191997397039259454017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41040511993058771358544045 15390191997397039259454017)
          ·
            refine ⟨11542643998047779444590513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15390191997397039259454017 11542643998047779444590513)
            ·
              refine ⟨8656982998535834583442885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11542643998047779444590513 8656982998535834583442885)
              ·
                refine ⟨1623184312225468984395541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8656982998535834583442885 1623184312225468984395541)
                ·
                  refine ⟨76086764635568858643541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1623184312225468984395541 76086764635568858643541)
                  ·
                    rfl

theorem cell22_666803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 6].length) (baseStart_666803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666803 prefixEnd_666803 := by exact prefixLift 666803
  have htrace : WordTrace (prefixWord ++ tailWord_666803) baseStart_666803 baseEnd_666803 := by
    simpa [prefixWord, tailWord_666803, baseEnd_666803] using wordTrace_append hprefix tailTrace_666803
  have hstable : (prefixWord ++ tailWord_666803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666803).length < 2 ^ (prefixWord ++ tailWord_666803).sum := by decide
  have hdescent : baseEnd_666803 < baseStart_666803 := by decide
  rcases family_descends (prefixWord ++ tailWord_666803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666833 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_666833 : Nat := 118140960795 + 666833 * 2 ^ 59
def prefixEnd_666833 : Nat := 4983230072969 + 3 ^ 40 * 666833 * 2
def baseEnd_666833 : Nat := 228270563519796497680531

theorem tailTrace_666833 : CollatzResearch.WordTrace tailWord_666833 prefixEnd_666833 228270563519796497680531 := by
  unfold tailWord_666833
  simp only [CollatzResearch.WordTrace]
  refine ⟨24321397593185401854581153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16214265062123601236387435 24321397593185401854581153)
  ·
    refine ⟨18241048194889051390935865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24321397593185401854581153 18241048194889051390935865)
    ·
      refine ⟨13680786146166788543201899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18241048194889051390935865 13680786146166788543201899)
      ·
        refine ⟨20521179219250182814802849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13680786146166788543201899 20521179219250182814802849)
        ·
          refine ⟨15390884414437637111102137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20521179219250182814802849 15390884414437637111102137)
          ·
            refine ⟨11543163310828227833326603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15390884414437637111102137 11543163310828227833326603)
            ·
              refine ⟨17314744966242341749989905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11543163310828227833326603 17314744966242341749989905)
              ·
                refine ⟨12986058724681756312492429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17314744966242341749989905 12986058724681756312492429)
                ·
                  refine ⟨4869772021755658617184661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12986058724681756312492429 4869772021755658617184661)
                  ·
                    refine ⟨228270563519796497680531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4869772021755658617184661 228270563519796497680531)
                    ·
                      rfl

theorem cell22_666833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_666833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666833 prefixEnd_666833 := by exact prefixLift 666833
  have htrace : WordTrace (prefixWord ++ tailWord_666833) baseStart_666833 baseEnd_666833 := by
    simpa [prefixWord, tailWord_666833, baseEnd_666833] using wordTrace_append hprefix tailTrace_666833
  have hstable : (prefixWord ++ tailWord_666833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666833).length < 2 ^ (prefixWord ++ tailWord_666833).sum := by decide
  have hdescent : baseEnd_666833 < baseStart_666833 := by decide
  rcases family_descends (prefixWord ++ tailWord_666833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666852 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_666852 : Nat := 118140960795 + 666852 * 2 ^ 59
def prefixEnd_666852 : Nat := 4983230072969 + 3 ^ 40 * 666852 * 2
def baseEnd_666852 : Nat := 228277067608086781455473

theorem tailTrace_666852 : CollatzResearch.WordTrace tailWord_666852 prefixEnd_666852 228277067608086781455473 := by
  unfold tailWord_666852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12161045290058284049761405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16214727053411045399681873 12161045290058284049761405)
  ·
    refine ⟨4560391983771856518660527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12161045290058284049761405 4560391983771856518660527)
    ·
      refine ⟨6840587975657784777990791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560391983771856518660527 6840587975657784777990791)
      ·
        refine ⟨10260881963486677166986187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840587975657784777990791 10260881963486677166986187)
        ·
          refine ⟨15391322945230015750479281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10260881963486677166986187 15391322945230015750479281)
          ·
            refine ⟨11543492208922511812859461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15391322945230015750479281 11543492208922511812859461)
            ·
              refine ⟨2164404789172970964911149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11543492208922511812859461 2164404789172970964911149)
              ·
                refine ⟨811651795939864111841681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2164404789172970964911149 811651795939864111841681)
                ·
                  refine ⟨608738846954898083881261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 811651795939864111841681 608738846954898083881261)
                  ·
                    refine ⟨228277067608086781455473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 608738846954898083881261 228277067608086781455473)
                    ·
                      rfl

theorem cell22_666852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_666852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666852 prefixEnd_666852 := by exact prefixLift 666852
  have htrace : WordTrace (prefixWord ++ tailWord_666852) baseStart_666852 baseEnd_666852 := by
    simpa [prefixWord, tailWord_666852, baseEnd_666852] using wordTrace_append hprefix tailTrace_666852
  have hstable : (prefixWord ++ tailWord_666852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666852).length < 2 ^ (prefixWord ++ tailWord_666852).sum := by decide
  have hdescent : baseEnd_666852 < baseStart_666852 := by decide
  rcases family_descends (prefixWord ++ tailWord_666852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666867 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 2, 4]
def baseStart_666867 : Nat := 118140960795 + 666867 * 2 ^ 59
def prefixEnd_666867 : Nat := 4983230072969 + 3 ^ 40 * 666867 * 2
def baseEnd_666867 : Nat := 228282202414631742330427

theorem tailTrace_666867 : CollatzResearch.WordTrace tailWord_666867 prefixEnd_666867 228282202414631742330427 := by
  unfold tailWord_666867
  simp only [CollatzResearch.WordTrace]
  refine ⟨24322637675062225661318855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16215091783374817107545903 24322637675062225661318855)
  ·
    refine ⟨36483956512593338491978283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24322637675062225661318855 36483956512593338491978283)
    ·
      refine ⟨54725934768890007737967425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36483956512593338491978283 54725934768890007737967425)
      ·
        refine ⟨41044451076667505803475569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54725934768890007737967425 41044451076667505803475569)
        ·
          refine ⟨30783338307500629352606677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41044451076667505803475569 30783338307500629352606677)
          ·
            refine ⟨721484491582046000451719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 30783338307500629352606677 721484491582046000451719)
            ·
              refine ⟨1082226737373069000677579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721484491582046000451719 1082226737373069000677579)
              ·
                refine ⟨1623340106059603501016369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082226737373069000677579 1623340106059603501016369)
                ·
                  refine ⟨1217505079544702625762277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1623340106059603501016369 1217505079544702625762277)
                  ·
                    refine ⟨228282202414631742330427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1217505079544702625762277 228282202414631742330427)
                    ·
                      rfl

theorem cell22_666867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 4].length) (baseStart_666867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666867 prefixEnd_666867 := by exact prefixLift 666867
  have htrace : WordTrace (prefixWord ++ tailWord_666867) baseStart_666867 baseEnd_666867 := by
    simpa [prefixWord, tailWord_666867, baseEnd_666867] using wordTrace_append hprefix tailTrace_666867
  have hstable : (prefixWord ++ tailWord_666867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666867).length < 2 ^ (prefixWord ++ tailWord_666867).sum := by decide
  have hdescent : baseEnd_666867 < baseStart_666867 := by decide
  rcases family_descends (prefixWord ++ tailWord_666867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666880 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 7, 3]
def baseStart_666880 : Nat := 118140960795 + 666880 * 2 ^ 59
def prefixEnd_666880 : Nat := 4983230072969 + 3 ^ 40 * 666880 * 2
def baseEnd_666880 : Nat := 228286652580304041755387

theorem tailTrace_666880 : CollatzResearch.WordTrace tailWord_666880 prefixEnd_666880 228286652580304041755387 := by
  unfold tailWord_666880
  simp only [CollatzResearch.WordTrace]
  refine ⟨12161555912007564440771047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16215407882676752587694729 12161555912007564440771047)
  ·
    refine ⟨18242333868011346661156571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12161555912007564440771047 18242333868011346661156571)
    ·
      refine ⟨27363500802017019991734857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18242333868011346661156571 27363500802017019991734857)
      ·
        refine ⟨20522625601512764993801143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27363500802017019991734857 20522625601512764993801143)
        ·
          refine ⟨30783938402269147490701715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20522625601512764993801143 30783938402269147490701715)
          ·
            refine ⟨46175907603403721236052573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30783938402269147490701715 46175907603403721236052573)
            ·
              refine ⟨17315965351276395463519715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46175907603403721236052573 17315965351276395463519715)
              ·
                refine ⟨25973948026914593195279573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17315965351276395463519715 25973948026914593195279573)
                ·
                  refine ⟨608764406880810778014365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 25973948026914593195279573 608764406880810778014365)
                  ·
                    refine ⟨228286652580304041755387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 608764406880810778014365 228286652580304041755387)
                    ·
                      rfl

theorem cell22_666880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_666880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666880 prefixEnd_666880 := by exact prefixLift 666880
  have htrace : WordTrace (prefixWord ++ tailWord_666880) baseStart_666880 baseEnd_666880 := by
    simpa [prefixWord, tailWord_666880, baseEnd_666880] using wordTrace_append hprefix tailTrace_666880
  have hstable : (prefixWord ++ tailWord_666880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666880).length < 2 ^ (prefixWord ++ tailWord_666880).sum := by decide
  have hdescent : baseEnd_666880 < baseStart_666880 := by decide
  rcases family_descends (prefixWord ++ tailWord_666880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666882 : List Nat := [3, 4, 1, 1, 3, 1, 9]
def baseStart_666882 : Nat := 118140960795 + 666882 * 2 ^ 59
def prefixEnd_666882 : Nat := 4983230072969 + 3 ^ 40 * 666882 * 2
def baseEnd_666882 : Nat := 8455086563747285303903

theorem tailTrace_666882 : CollatzResearch.WordTrace tailWord_666882 prefixEnd_666882 8455086563747285303903 := by
  unfold tailWord_666882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6080796192501970805778725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16215456513338588815409933 6080796192501970805778725)
  ·
    refine ⟨1140149286094119526083511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6080796192501970805778725 1140149286094119526083511)
    ·
      refine ⟨1710223929141179289125267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1140149286094119526083511 1710223929141179289125267)
      ·
        refine ⟨2565335893711768933687901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1710223929141179289125267 2565335893711768933687901)
        ·
          refine ⟨962000960141913350132963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2565335893711768933687901 962000960141913350132963)
          ·
            refine ⟨1443001440212870025199445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962000960141913350132963 1443001440212870025199445)
            ·
              refine ⟨8455086563747285303903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1443001440212870025199445 8455086563747285303903)
              ·
                rfl

theorem cell22_666882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 9].length) (baseStart_666882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666882 prefixEnd_666882 := by exact prefixLift 666882
  have htrace : WordTrace (prefixWord ++ tailWord_666882) baseStart_666882 baseEnd_666882 := by
    simpa [prefixWord, tailWord_666882, baseEnd_666882] using wordTrace_append hprefix tailTrace_666882
  have hstable : (prefixWord ++ tailWord_666882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666882).length < 2 ^ (prefixWord ++ tailWord_666882).sum := by decide
  have hdescent : baseEnd_666882 < baseStart_666882 := by decide
  rcases family_descends (prefixWord ++ tailWord_666882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666897 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 3, 3]
def baseStart_666897 : Nat := 118140960795 + 666897 * 2 ^ 59
def prefixEnd_666897 : Nat := 4983230072969 + 3 ^ 40 * 666897 * 2
def baseEnd_666897 : Nat := 228292472027721664080335

theorem tailTrace_666897 : CollatzResearch.WordTrace tailWord_666897 prefixEnd_666897 228292472027721664080335 := by
  unfold tailWord_666897
  simp only [CollatzResearch.WordTrace]
  refine ⟨24323731864953540784910945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16215821243302360523273963 24323731864953540784910945)
  ·
    refine ⟨18242798898715155588683209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24323731864953540784910945 18242798898715155588683209)
    ·
      refine ⟨13682099174036366691512407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18242798898715155588683209 13682099174036366691512407)
      ·
        refine ⟨20523148761054550037268611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13682099174036366691512407 20523148761054550037268611)
        ·
          refine ⟨30784723141581825055902917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20523148761054550037268611 30784723141581825055902917)
          ·
            refine ⟨5772135589046592197981797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30784723141581825055902917 5772135589046592197981797)
            ·
              refine ⟨1082275422946236037121587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5772135589046592197981797 1082275422946236037121587)
              ·
                refine ⟨1623413134419354055682381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082275422946236037121587 1623413134419354055682381)
                ·
                  refine ⟨608779925407257770880893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1623413134419354055682381 608779925407257770880893)
                  ·
                    refine ⟨228292472027721664080335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 608779925407257770880893 228292472027721664080335)
                    ·
                      rfl

theorem cell22_666897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_666897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666897 prefixEnd_666897 := by exact prefixLift 666897
  have htrace : WordTrace (prefixWord ++ tailWord_666897) baseStart_666897 baseEnd_666897 := by
    simpa [prefixWord, tailWord_666897, baseEnd_666897] using wordTrace_append hprefix tailTrace_666897
  have hstable : (prefixWord ++ tailWord_666897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666897).length < 2 ^ (prefixWord ++ tailWord_666897).sum := by decide
  have hdescent : baseEnd_666897 < baseStart_666897 := by decide
  rcases family_descends (prefixWord ++ tailWord_666897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666931 : List Nat := [1, 1, 1, 2, 5, 4, 1, 3, 1, 3]
def baseStart_666931 : Nat := 118140960795 + 666931 * 2 ^ 59
def prefixEnd_666931 : Nat := 4983230072969 + 3 ^ 40 * 666931 * 2
def baseEnd_666931 : Nat := 228304110922556908730231

theorem tailTrace_666931 : CollatzResearch.WordTrace tailWord_666931 prefixEnd_666931 228304110922556908730231 := by
  unfold tailWord_666931
  simp only [CollatzResearch.WordTrace]
  refine ⟨24324971946830364591648647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16216647964553576394432431 24324971946830364591648647)
  ·
    refine ⟨36487457920245546887472971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24324971946830364591648647 36487457920245546887472971)
    ·
      refine ⟨54731186880368320331209457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36487457920245546887472971 54731186880368320331209457)
      ·
        refine ⟨41048390160276240248407093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54731186880368320331209457 41048390160276240248407093)
        ·
          refine ⟨3848286577525897523288165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41048390160276240248407093 3848286577525897523288165)
          ·
            refine ⟨721553733286105785616531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3848286577525897523288165 721553733286105785616531)
            ·
              refine ⟨1082330599929158678424797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721553733286105785616531 1082330599929158678424797)
              ·
                refine ⟨405873974973434504409299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1082330599929158678424797 405873974973434504409299)
                ·
                  refine ⟨608810962460151756613949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405873974973434504409299 608810962460151756613949)
                  ·
                    refine ⟨228304110922556908730231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 608810962460151756613949 228304110922556908730231)
                    ·
                      rfl

theorem cell22_666931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 3].length) (baseStart_666931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_666931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_666931 prefixEnd_666931 := by exact prefixLift 666931
  have htrace : WordTrace (prefixWord ++ tailWord_666931) baseStart_666931 baseEnd_666931 := by
    simpa [prefixWord, tailWord_666931, baseEnd_666931] using wordTrace_append hprefix tailTrace_666931
  have hstable : (prefixWord ++ tailWord_666931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666931).length < 2 ^ (prefixWord ++ tailWord_666931).sum := by decide
  have hdescent : baseEnd_666931 < baseStart_666931 := by decide
  rcases family_descends (prefixWord ++ tailWord_666931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667004 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_667004 : Nat := 118140960795 + 667004 * 2 ^ 59
def prefixEnd_667004 : Nat := 4983230072969 + 3 ^ 40 * 667004 * 2
def baseEnd_667004 : Nat := 228329100314409051655007

theorem tailTrace_667004 : CollatzResearch.WordTrace tailWord_667004 prefixEnd_667004 228329100314409051655007 := by
  unfold tailWord_667004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12163817237782949029528033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16218422983710598706037377 12163817237782949029528033)
  ·
    refine ⟨9122862928337211772146025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12163817237782949029528033 9122862928337211772146025)
    ·
      refine ⟨6842147196252908829109519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9122862928337211772146025 6842147196252908829109519)
      ·
        refine ⟨10263220794379363243664279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6842147196252908829109519 10263220794379363243664279)
        ·
          refine ⟨15394831191569044865496419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10263220794379363243664279 15394831191569044865496419)
          ·
            refine ⟨23092246787353567298244629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15394831191569044865496419 23092246787353567298244629)
            ·
              refine ⟨1082449068157198467105217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23092246787353567298244629 1082449068157198467105217)
              ·
                refine ⟨811836801117898850328913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1082449068157198467105217 811836801117898850328913)
                ·
                  refine ⟨608877600838424137746685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 811836801117898850328913 608877600838424137746685)
                  ·
                    refine ⟨228329100314409051655007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 608877600838424137746685 228329100314409051655007)
                    ·
                      rfl

theorem cell22_667004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_667004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667004 prefixEnd_667004 := by exact prefixLift 667004
  have htrace : WordTrace (prefixWord ++ tailWord_667004) baseStart_667004 baseEnd_667004 := by
    simpa [prefixWord, tailWord_667004, baseEnd_667004] using wordTrace_append hprefix tailTrace_667004
  have hstable : (prefixWord ++ tailWord_667004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667004).length < 2 ^ (prefixWord ++ tailWord_667004).sum := by decide
  have hdescent : baseEnd_667004 < baseStart_667004 := by decide
  rcases family_descends (prefixWord ++ tailWord_667004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667079 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 5]
def baseStart_667079 : Nat := 118140960795 + 667079 * 2 ^ 59
def prefixEnd_667079 : Nat := 4983230072969 + 3 ^ 40 * 667079 * 2
def baseEnd_667079 : Nat := 76118258115711285343259

theorem tailTrace_667079 : CollatzResearch.WordTrace tailWord_667079 prefixEnd_667079 76118258115711285343259 := by
  unfold tailWord_667079
  simp only [CollatzResearch.WordTrace]
  refine ⟨24330369950294185868036291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16220246633529457245357527 24330369950294185868036291)
  ·
    refine ⟨36495554925441278802054437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24330369950294185868036291 36495554925441278802054437)
    ·
      refine ⟨6842916548520239775385207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36495554925441278802054437 6842916548520239775385207)
      ·
        refine ⟨10264374822780359663077811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6842916548520239775385207 10264374822780359663077811)
        ·
          refine ⟨15396562234170539494616717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10264374822780359663077811 15396562234170539494616717)
          ·
            refine ⟨5773710837813952310481269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15396562234170539494616717 5773710837813952310481269)
            ·
              refine ⟨541285391045058029107619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5773710837813952310481269 541285391045058029107619)
              ·
                refine ⟨811928086567587043661429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541285391045058029107619 811928086567587043661429)
                ·
                  refine ⟨76118258115711285343259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 811928086567587043661429 76118258115711285343259)
                  ·
                    rfl

theorem cell22_667079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 5].length) (baseStart_667079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667079 prefixEnd_667079 := by exact prefixLift 667079
  have htrace : WordTrace (prefixWord ++ tailWord_667079) baseStart_667079 baseEnd_667079 := by
    simpa [prefixWord, tailWord_667079, baseEnd_667079] using wordTrace_append hprefix tailTrace_667079
  have hstable : (prefixWord ++ tailWord_667079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667079).length < 2 ^ (prefixWord ++ tailWord_667079).sum := by decide
  have hdescent : baseEnd_667079 < baseStart_667079 := by decide
  rcases family_descends (prefixWord ++ tailWord_667079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667184 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 3, 3]
def baseStart_667184 : Nat := 118140960795 + 667184 * 2 ^ 59
def prefixEnd_667184 : Nat := 4983230072969 + 3 ^ 40 * 667184 * 2
def baseEnd_667184 : Nat := 228390717992948582154455

theorem tailTrace_667184 : CollatzResearch.WordTrace tailWord_667184 prefixEnd_667184 228390717992948582154455 := by
  unfold tailWord_667184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12167099807456894400304303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16222799743275859200405737 12167099807456894400304303)
  ·
    refine ⟨18250649711185341600456455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12167099807456894400304303 18250649711185341600456455)
    ·
      refine ⟨27375974566778012400684683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18250649711185341600456455 27375974566778012400684683)
      ·
        refine ⟨41063961850167018601027025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27375974566778012400684683 41063961850167018601027025)
        ·
          refine ⟨30797971387625263950770269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41063961850167018601027025 30797971387625263950770269)
          ·
            refine ⟨11549239270359473981538851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30797971387625263950770269 11549239270359473981538851)
            ·
              refine ⟨17323858905539210972308277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11549239270359473981538851 17323858905539210972308277)
              ·
                refine ⟨1624111772394301028653901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17323858905539210972308277 1624111772394301028653901)
                ·
                  refine ⟨609041914647862885745213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1624111772394301028653901 609041914647862885745213)
                  ·
                    refine ⟨228390717992948582154455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609041914647862885745213 228390717992948582154455)
                    ·
                      rfl

theorem cell22_667184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_667184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667184 prefixEnd_667184 := by exact prefixLift 667184
  have htrace : WordTrace (prefixWord ++ tailWord_667184) baseStart_667184 baseEnd_667184 := by
    simpa [prefixWord, tailWord_667184, baseEnd_667184] using wordTrace_append hprefix tailTrace_667184
  have hstable : (prefixWord ++ tailWord_667184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667184).length < 2 ^ (prefixWord ++ tailWord_667184).sum := by decide
  have hdescent : baseEnd_667184 < baseStart_667184 := by decide
  rcases family_descends (prefixWord ++ tailWord_667184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667201 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 3, 3]
def baseStart_667201 : Nat := 118140960795 + 667201 * 2 ^ 59
def prefixEnd_667201 : Nat := 4983230072969 + 3 ^ 40 * 667201 * 2
def baseEnd_667201 : Nat := 228396537440366204479403

theorem tailTrace_667201 : CollatzResearch.WordTrace tailWord_667201 prefixEnd_667201 228396537440366204479403 := by
  unfold tailWord_667201
  simp only [CollatzResearch.WordTrace]
  refine ⟨24334819655852200703977457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16223213103901467135984971 24334819655852200703977457)
  ·
    refine ⟨18251114741889150527983093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24334819655852200703977457 18251114741889150527983093)
    ·
      refine ⟨1711042007052107861998415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18251114741889150527983093 1711042007052107861998415)
      ·
        refine ⟨2566563010578161792997623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711042007052107861998415 2566563010578161792997623)
        ·
          refine ⟨3849844515867242689496435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566563010578161792997623 3849844515867242689496435)
          ·
            refine ⟨5774766773800864034244653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849844515867242689496435 5774766773800864034244653)
            ·
              refine ⟨2165537540175324012841745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5774766773800864034244653 2165537540175324012841745)
              ·
                refine ⟨1624153155131493009631309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165537540175324012841745 1624153155131493009631309)
                ·
                  refine ⟨609057433174309878611741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1624153155131493009631309 609057433174309878611741)
                  ·
                    refine ⟨228396537440366204479403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609057433174309878611741 228396537440366204479403)
                    ·
                      rfl

theorem cell22_667201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_667201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667201 prefixEnd_667201 := by exact prefixLift 667201
  have htrace : WordTrace (prefixWord ++ tailWord_667201) baseStart_667201 baseEnd_667201 := by
    simpa [prefixWord, tailWord_667201, baseEnd_667201] using wordTrace_append hprefix tailTrace_667201
  have hstable : (prefixWord ++ tailWord_667201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667201).length < 2 ^ (prefixWord ++ tailWord_667201).sum := by decide
  have hdescent : baseEnd_667201 < baseStart_667201 := by decide
  rcases family_descends (prefixWord ++ tailWord_667201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667218 : List Nat := [3, 2, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_667218 : Nat := 118140960795 + 667218 * 2 ^ 59
def prefixEnd_667218 : Nat := 4983230072969 + 3 ^ 40 * 667218 * 2
def baseEnd_667218 : Nat := 228402356887783826804351

theorem tailTrace_667218 : CollatzResearch.WordTrace tailWord_667218 prefixEnd_667218 228402356887783826804351 := by
  unfold tailWord_667218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083859924197653151836577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16223626464527075071564205 6083859924197653151836577)
  ·
    refine ⟨4562894943148239863877433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6083859924197653151836577 4562894943148239863877433)
    ·
      refine ⟨3422171207361179897908075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4562894943148239863877433 3422171207361179897908075)
      ·
        refine ⟨5133256811041769846862113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3422171207361179897908075 5133256811041769846862113)
        ·
          refine ⟨3849942608281327385146585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5133256811041769846862113 3849942608281327385146585)
          ·
            refine ⟨2887456956210995538859939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3849942608281327385146585 2887456956210995538859939)
            ·
              refine ⟨4331185434316493308289909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2887456956210995538859939 4331185434316493308289909)
              ·
                refine ⟨406048634467171247652179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4331185434316493308289909 406048634467171247652179)
                ·
                  refine ⟨609072951700756871478269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406048634467171247652179 609072951700756871478269)
                  ·
                    refine ⟨228402356887783826804351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609072951700756871478269 228402356887783826804351)
                    ·
                      rfl

theorem cell22_667218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_667218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667218 prefixEnd_667218 := by exact prefixLift 667218
  have htrace : WordTrace (prefixWord ++ tailWord_667218) baseStart_667218 baseEnd_667218 := by
    simpa [prefixWord, tailWord_667218, baseEnd_667218] using wordTrace_append hprefix tailTrace_667218
  have hstable : (prefixWord ++ tailWord_667218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667218).length < 2 ^ (prefixWord ++ tailWord_667218).sum := by decide
  have hdescent : baseEnd_667218 < baseStart_667218 := by decide
  rcases family_descends (prefixWord ++ tailWord_667218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667261 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_667261 : Nat := 118140960795 + 667261 * 2 ^ 59
def prefixEnd_667261 : Nat := 4983230072969 + 3 ^ 40 * 667261 * 2
def baseEnd_667261 : Nat := 228417076666546047979219

theorem tailTrace_667261 : CollatzResearch.WordTrace tailWord_667261 prefixEnd_667261 228417076666546047979219 := by
  unfold tailWord_667261
  simp only [CollatzResearch.WordTrace]
  refine ⟨24337008035634830951161637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16224672023756553967441091 24337008035634830951161637)
  ·
    refine ⟨4563189006681530803342807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24337008035634830951161637 4563189006681530803342807)
    ·
      refine ⟨6844783510022296205014211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4563189006681530803342807 6844783510022296205014211)
      ·
        refine ⟨10267175265033444307521317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6844783510022296205014211 10267175265033444307521317)
        ·
          refine ⟨1925095362193770807660247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10267175265033444307521317 1925095362193770807660247)
          ·
            refine ⟨2887643043290656211490371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925095362193770807660247 2887643043290656211490371)
            ·
              refine ⟨4331464564935984317235557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2887643043290656211490371 4331464564935984317235557)
              ·
                refine ⟨812149605925497059481667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4331464564935984317235557 812149605925497059481667)
                ·
                  refine ⟨1218224408888245589222501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812149605925497059481667 1218224408888245589222501)
                  ·
                    refine ⟨228417076666546047979219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1218224408888245589222501 228417076666546047979219)
                    ·
                      rfl

theorem cell22_667261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_667261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667261 prefixEnd_667261 := by exact prefixLift 667261
  have htrace : WordTrace (prefixWord ++ tailWord_667261) baseStart_667261 baseEnd_667261 := by
    simpa [prefixWord, tailWord_667261, baseEnd_667261] using wordTrace_append hprefix tailTrace_667261
  have hstable : (prefixWord ++ tailWord_667261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667261).length < 2 ^ (prefixWord ++ tailWord_667261).sum := by decide
  have hdescent : baseEnd_667261 < baseStart_667261 := by decide
  rcases family_descends (prefixWord ++ tailWord_667261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667439 : List Nat := [1, 1, 2, 1, 2, 1, 2, 12]
def baseStart_667439 : Nat := 118140960795 + 667439 * 2 ^ 59
def prefixEnd_667439 : Nat := 4983230072969 + 3 ^ 40 * 667439 * 2
def baseEnd_667439 : Nat := 25386445522690324114297

theorem tailTrace_667439 : CollatzResearch.WordTrace tailWord_667439 prefixEnd_667439 25386445522690324114297 := by
  unfold tailWord_667439
  simp only [CollatzResearch.WordTrace]
  refine ⟨24343500228989967351141371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16229000152659978234094247 24343500228989967351141371)
  ·
    refine ⟨36515250343484951026712057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24343500228989967351141371 36515250343484951026712057)
    ·
      refine ⟨27386437757613713270034043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36515250343484951026712057 27386437757613713270034043)
      ·
        refine ⟨41079656636420569905051065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27386437757613713270034043 41079656636420569905051065)
        ·
          refine ⟨30809742477315427428788299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41079656636420569905051065 30809742477315427428788299)
          ·
            refine ⟨46214613715973141143182449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30809742477315427428788299 46214613715973141143182449)
            ·
              refine ⟨34660960286979855857386837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46214613715973141143182449 34660960286979855857386837)
              ·
                refine ⟨25386445522690324114297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 34660960286979855857386837 25386445522690324114297)
                ·
                  rfl

theorem cell22_667439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 12].length) (baseStart_667439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667439 prefixEnd_667439 := by exact prefixLift 667439
  have htrace : WordTrace (prefixWord ++ tailWord_667439) baseStart_667439 baseEnd_667439 := by
    simpa [prefixWord, tailWord_667439, baseEnd_667439] using wordTrace_append hprefix tailTrace_667439
  have hstable : (prefixWord ++ tailWord_667439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667439).length < 2 ^ (prefixWord ++ tailWord_667439).sum := by decide
  have hdescent : baseEnd_667439 < baseStart_667439 := by decide
  rcases family_descends (prefixWord ++ tailWord_667439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667441 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_667441 : Nat := 118140960795 + 667441 * 2 ^ 59
def prefixEnd_667441 : Nat := 4983230072969 + 3 ^ 40 * 667441 * 2
def baseEnd_667441 : Nat := 228478694345085578478667

theorem tailTrace_667441 : CollatzResearch.WordTrace tailWord_667441 prefixEnd_667441 228478694345085578478667 := by
  unfold tailWord_667441
  simp only [CollatzResearch.WordTrace]
  refine ⟨24343573174982721692714177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16229048783321814461809451 24343573174982721692714177)
  ·
    refine ⟨18257679881237041269535633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24343573174982721692714177 18257679881237041269535633)
    ·
      refine ⟨13693259910927780952151725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18257679881237041269535633 13693259910927780952151725)
      ·
        refine ⟨5134972466597917857056897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13693259910927780952151725 5134972466597917857056897)
        ·
          refine ⟨3851229349948438392792673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5134972466597917857056897 3851229349948438392792673)
          ·
            refine ⟨2888422012461328794594505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3851229349948438392792673 2888422012461328794594505)
            ·
              refine ⟨2166316509345996595945879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888422012461328794594505 2166316509345996595945879)
              ·
                refine ⟨3249474764018994893918819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166316509345996595945879 3249474764018994893918819)
                ·
                  refine ⟨4874212146028492340878229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3249474764018994893918819 4874212146028492340878229)
                  ·
                    refine ⟨228478694345085578478667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4874212146028492340878229 228478694345085578478667)
                    ·
                      rfl

theorem cell22_667441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_667441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667441 prefixEnd_667441 := by exact prefixLift 667441
  have htrace : WordTrace (prefixWord ++ tailWord_667441) baseStart_667441 baseEnd_667441 := by
    simpa [prefixWord, tailWord_667441, baseEnd_667441] using wordTrace_append hprefix tailTrace_667441
  have hstable : (prefixWord ++ tailWord_667441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667441).length < 2 ^ (prefixWord ++ tailWord_667441).sum := by decide
  have hdescent : baseEnd_667441 < baseStart_667441 := by decide
  rcases family_descends (prefixWord ++ tailWord_667441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667462 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_667462 : Nat := 118140960795 + 667462 * 2 ^ 59
def prefixEnd_667462 : Nat := 4983230072969 + 3 ^ 40 * 667462 * 2
def baseEnd_667462 : Nat := 76161961024749507901201

theorem tailTrace_667462 : CollatzResearch.WordTrace tailWord_667462 prefixEnd_667462 76161961024749507901201 := by
  unfold tailWord_667462
  simp only [CollatzResearch.WordTrace]
  refine ⟨760760597122082571225895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16229559405271094852819093 760760597122082571225895)
  ·
    refine ⟨1141140895683123856838843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 760760597122082571225895 1141140895683123856838843)
    ·
      refine ⟨1711711343524685785258265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141140895683123856838843 1711711343524685785258265)
      ·
        refine ⟨1283783507643514338943699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1711711343524685785258265 1283783507643514338943699)
        ·
          refine ⟨1925675261465271508415549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283783507643514338943699 1925675261465271508415549)
          ·
            refine ⟨722128223049476815655831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1925675261465271508415549 722128223049476815655831)
            ·
              refine ⟨1083192334574215223483747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722128223049476815655831 1083192334574215223483747)
              ·
                refine ⟨1624788501861322835225621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083192334574215223483747 1624788501861322835225621)
                ·
                  refine ⟨76161961024749507901201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1624788501861322835225621 76161961024749507901201)
                  ·
                    rfl

theorem cell22_667462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_667462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667462 prefixEnd_667462 := by exact prefixLift 667462
  have htrace : WordTrace (prefixWord ++ tailWord_667462) baseStart_667462 baseEnd_667462 := by
    simpa [prefixWord, tailWord_667462, baseEnd_667462] using wordTrace_append hprefix tailTrace_667462
  have hstable : (prefixWord ++ tailWord_667462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667462).length < 2 ^ (prefixWord ++ tailWord_667462).sum := by decide
  have hdescent : baseEnd_667462 < baseStart_667462 := by decide
  rcases family_descends (prefixWord ++ tailWord_667462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667477 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_667477 : Nat := 118140960795 + 667477 * 2 ^ 59
def prefixEnd_667477 : Nat := 4983230072969 + 3 ^ 40 * 667477 * 2
def baseEnd_667477 : Nat := 228491017880793484578557

theorem tailTrace_667477 : CollatzResearch.WordTrace tailWord_667477 prefixEnd_667477 228491017880793484578557 := by
  unfold tailWord_667477
  simp only [CollatzResearch.WordTrace]
  refine ⟨24344886202852299841024685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16229924135234866560683123 24344886202852299841024685)
  ·
    refine ⟨9129332326069612440384257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24344886202852299841024685 9129332326069612440384257)
    ·
      refine ⟨6846999244552209330288193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9129332326069612440384257 6846999244552209330288193)
      ·
        refine ⟨5135249433414156997716145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6846999244552209330288193 5135249433414156997716145)
        ·
          refine ⟨3851437075060617748287109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5135249433414156997716145 3851437075060617748287109)
          ·
            refine ⟨722144451573865827803833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3851437075060617748287109 722144451573865827803833)
            ·
              refine ⟨541608338680399370852875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722144451573865827803833 541608338680399370852875)
              ·
                refine ⟨812412508020599056279313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541608338680399370852875 812412508020599056279313)
                ·
                  refine ⟨609309381015449292209485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 812412508020599056279313 609309381015449292209485)
                  ·
                    refine ⟨228491017880793484578557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609309381015449292209485 228491017880793484578557)
                    ·
                      rfl

theorem cell22_667477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_667477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667477 prefixEnd_667477 := by exact prefixLift 667477
  have htrace : WordTrace (prefixWord ++ tailWord_667477) baseStart_667477 baseEnd_667477 := by
    simpa [prefixWord, tailWord_667477, baseEnd_667477] using wordTrace_append hprefix tailTrace_667477
  have hstable : (prefixWord ++ tailWord_667477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667477).length < 2 ^ (prefixWord ++ tailWord_667477).sum := by decide
  have hdescent : baseEnd_667477 < baseStart_667477 := by decide
  rcases family_descends (prefixWord ++ tailWord_667477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667501 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 9]
def baseStart_667501 : Nat := 118140960795 + 667501 * 2 ^ 59
def prefixEnd_667501 : Nat := 4983230072969 + 3 ^ 40 * 667501 * 2
def baseEnd_667501 : Nat := 76166411190421807326161

theorem tailTrace_667501 : CollatzResearch.WordTrace tailWord_667501 prefixEnd_667501 76166411190421807326161 := by
  unfold tailWord_667501
  simp only [CollatzResearch.WordTrace]
  refine ⟨24345761554765351939898357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16230507703176901293265571 24345761554765351939898357)
  ·
    refine ⟨2282415145759251744365471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24345761554765351939898357 2282415145759251744365471)
    ·
      refine ⟨3423622718638877616548207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2282415145759251744365471 3423622718638877616548207)
      ·
        refine ⟨5135434077958316424822311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3423622718638877616548207 5135434077958316424822311)
        ·
          refine ⟨7703151116937474637233467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135434077958316424822311 7703151116937474637233467)
          ·
            refine ⟨11554726675406211955850201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703151116937474637233467 11554726675406211955850201)
            ·
              refine ⟨8666045006554658966887651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11554726675406211955850201 8666045006554658966887651)
              ·
                refine ⟨12999067509831988450331477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8666045006554658966887651 12999067509831988450331477)
                ·
                  refine ⟨76166411190421807326161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12999067509831988450331477 76166411190421807326161)
                  ·
                    rfl

theorem cell22_667501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_667501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667501 prefixEnd_667501 := by exact prefixLift 667501
  have htrace : WordTrace (prefixWord ++ tailWord_667501) baseStart_667501 baseEnd_667501 := by
    simpa [prefixWord, tailWord_667501, baseEnd_667501] using wordTrace_append hprefix tailTrace_667501
  have hstable : (prefixWord ++ tailWord_667501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667501).length < 2 ^ (prefixWord ++ tailWord_667501).sum := by decide
  have hdescent : baseEnd_667501 < baseStart_667501 := by decide
  rcases family_descends (prefixWord ++ tailWord_667501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667505 : List Nat := [1, 2, 2, 2, 1, 3, 2, 5, 1, 3]
def baseStart_667505 : Nat := 118140960795 + 667505 * 2 ^ 59
def prefixEnd_667505 : Nat := 4983230072969 + 3 ^ 40 * 667505 * 2
def baseEnd_667505 : Nat := 228500602853010744878471

theorem tailTrace_667505 : CollatzResearch.WordTrace tailWord_667505 prefixEnd_667505 228500602853010744878471 := by
  unfold tailWord_667505
  simp only [CollatzResearch.WordTrace]
  refine ⟨24345907446750860623043969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16230604964500573748695979 24345907446750860623043969)
  ·
    refine ⟨18259430585063145467282977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24345907446750860623043969 18259430585063145467282977)
    ·
      refine ⟨13694572938797359100462233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18259430585063145467282977 13694572938797359100462233)
      ·
        refine ⟨10270929704098019325346675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13694572938797359100462233 10270929704098019325346675)
        ·
          refine ⟨15406394556147028988020013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10270929704098019325346675 15406394556147028988020013)
          ·
            refine ⟨5777397958555135870507505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15406394556147028988020013 5777397958555135870507505)
            ·
              refine ⟨4333048468916351902880629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5777397958555135870507505 4333048468916351902880629)
              ·
                refine ⟨406223293960907990895059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4333048468916351902880629 406223293960907990895059)
                ·
                  refine ⟨609334940941361986342589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406223293960907990895059 609334940941361986342589)
                  ·
                    refine ⟨228500602853010744878471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609334940941361986342589 228500602853010744878471)
                    ·
                      rfl

theorem cell22_667505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_667505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667505 prefixEnd_667505 := by exact prefixLift 667505
  have htrace : WordTrace (prefixWord ++ tailWord_667505) baseStart_667505 baseEnd_667505 := by
    simpa [prefixWord, tailWord_667505, baseEnd_667505] using wordTrace_append hprefix tailTrace_667505
  have hstable : (prefixWord ++ tailWord_667505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667505).length < 2 ^ (prefixWord ++ tailWord_667505).sum := by decide
  have hdescent : baseEnd_667505 < baseStart_667505 := by decide
  rcases family_descends (prefixWord ++ tailWord_667505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667561 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_667561 : Nat := 118140960795 + 667561 * 2 ^ 59
def prefixEnd_667561 : Nat := 4983230072969 + 3 ^ 40 * 667561 * 2
def baseEnd_667561 : Nat := 228519772797445265478299

theorem tailTrace_667561 : CollatzResearch.WordTrace tailWord_667561 prefixEnd_667561 228519772797445265478299 := by
  unfold tailWord_667561
  simp only [CollatzResearch.WordTrace]
  refine ⟨24347949934547982187082537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16231966623031988124721691 24347949934547982187082537)
  ·
    refine ⟨18260962450910986640311903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24347949934547982187082537 18260962450910986640311903)
    ·
      refine ⟨27391443676366479960467855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18260962450910986640311903 27391443676366479960467855)
      ·
        refine ⟨41087165514549719940701783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27391443676366479960467855 41087165514549719940701783)
        ·
          refine ⟨61630748271824579911052675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41087165514549719940701783 61630748271824579911052675)
          ·
            refine ⟨92446122407736869866579013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61630748271824579911052675 92446122407736869866579013)
            ·
              refine ⟨17333647951450663099983565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92446122407736869866579013 17333647951450663099983565)
              ·
                refine ⟨6500117981793998662493837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17333647951450663099983565 6500117981793998662493837)
                ·
                  refine ⟨2437544243172749498435189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6500117981793998662493837 2437544243172749498435189)
                  ·
                    refine ⟨228519772797445265478299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2437544243172749498435189 228519772797445265478299)
                    ·
                      rfl

theorem cell22_667561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_667561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667561 prefixEnd_667561 := by exact prefixLift 667561
  have htrace : WordTrace (prefixWord ++ tailWord_667561) baseStart_667561 baseEnd_667561 := by
    simpa [prefixWord, tailWord_667561, baseEnd_667561] using wordTrace_append hprefix tailTrace_667561
  have hstable : (prefixWord ++ tailWord_667561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667561).length < 2 ^ (prefixWord ++ tailWord_667561).sum := by decide
  have hdescent : baseEnd_667561 < baseStart_667561 := by decide
  rcases family_descends (prefixWord ++ tailWord_667561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667591 : List Nat := [1, 1, 4, 1, 1, 2, 1, 11]
def baseStart_667591 : Nat := 118140960795 + 667591 * 2 ^ 59
def prefixEnd_667591 : Nat := 4983230072969 + 3 ^ 40 * 667591 * 2
def baseEnd_667591 : Nat := 25392226934503909692023

theorem tailTrace_667591 : CollatzResearch.WordTrace tailWord_667591 prefixEnd_667591 25392226934503909692023 := by
  unfold tailWord_667591
  simp only [CollatzResearch.WordTrace]
  refine ⟨24349044124439297310674627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16232696082959531540449751 24349044124439297310674627)
  ·
    refine ⟨36523566186658945966011941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24349044124439297310674627 36523566186658945966011941)
    ·
      refine ⟨6848168659998552368627239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36523566186658945966011941 6848168659998552368627239)
      ·
        refine ⟨10272252989997828552940859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848168659998552368627239 10272252989997828552940859)
        ·
          refine ⟨15408379484996742829411289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10272252989997828552940859 15408379484996742829411289)
          ·
            refine ⟨11556284613747557122058467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15408379484996742829411289 11556284613747557122058467)
            ·
              refine ⟨17334426920621335683087701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11556284613747557122058467 17334426920621335683087701)
              ·
                refine ⟨25392226934503909692023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 17334426920621335683087701 25392226934503909692023)
                ·
                  rfl

theorem cell22_667591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 11].length) (baseStart_667591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667591 prefixEnd_667591 := by exact prefixLift 667591
  have htrace : WordTrace (prefixWord ++ tailWord_667591) baseStart_667591 baseEnd_667591 := by
    simpa [prefixWord, tailWord_667591, baseEnd_667591] using wordTrace_append hprefix tailTrace_667591
  have hstable : (prefixWord ++ tailWord_667591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667591).length < 2 ^ (prefixWord ++ tailWord_667591).sum := by decide
  have hdescent : baseEnd_667591 < baseStart_667591 := by decide
  rcases family_descends (prefixWord ++ tailWord_667591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667640 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 3, 3]
def baseStart_667640 : Nat := 118140960795 + 667640 * 2 ^ 59
def prefixEnd_667640 : Nat := 4983230072969 + 3 ^ 40 * 667640 * 2
def baseEnd_667640 : Nat := 228546816111915392753057

theorem tailTrace_667640 : CollatzResearch.WordTrace tailWord_667640 prefixEnd_667640 228546816111915392753057 := by
  unfold tailWord_667640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12175415650630889339604187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16233887534174519119472249 12175415650630889339604187)
  ·
    refine ⟨18263123475946334009406281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12175415650630889339604187 18263123475946334009406281)
    ·
      refine ⟨13697342606959750507054711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18263123475946334009406281 13697342606959750507054711)
      ·
        refine ⟨20546013910439625760582067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13697342606959750507054711 20546013910439625760582067)
        ·
          refine ⟨30819020865659438640873101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20546013910439625760582067 30819020865659438640873101)
          ·
            refine ⟨11557132824622289490327413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30819020865659438640873101 11557132824622289490327413)
            ·
              refine ⟨1083481202308339639718195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11557132824622289490327413 1083481202308339639718195)
              ·
                refine ⟨1625221803462509459577293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083481202308339639718195 1625221803462509459577293)
                ·
                  refine ⟨609458176298441047341485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1625221803462509459577293 609458176298441047341485)
                  ·
                    refine ⟨228546816111915392753057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609458176298441047341485 228546816111915392753057)
                    ·
                      rfl

theorem cell22_667640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_667640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667640 prefixEnd_667640 := by exact prefixLift 667640
  have htrace : WordTrace (prefixWord ++ tailWord_667640) baseStart_667640 baseEnd_667640 := by
    simpa [prefixWord, tailWord_667640, baseEnd_667640] using wordTrace_append hprefix tailTrace_667640
  have hstable : (prefixWord ++ tailWord_667640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667640).length < 2 ^ (prefixWord ++ tailWord_667640).sum := by decide
  have hdescent : baseEnd_667640 < baseStart_667640 := by decide
  rcases family_descends (prefixWord ++ tailWord_667640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667646 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_667646 : Nat := 118140960795 + 667646 * 2 ^ 59
def prefixEnd_667646 : Nat := 4983230072969 + 3 ^ 40 * 667646 * 2
def baseEnd_667646 : Nat := 228548870034533377103039

theorem tailTrace_667646 : CollatzResearch.WordTrace tailWord_667646 prefixEnd_667646 228548870034533377103039 := by
  unfold tailWord_667646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043881267405005212990849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16234033426160027802617861 3043881267405005212990849)
  ·
    refine ⟨2282910950553753909743137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3043881267405005212990849 2282910950553753909743137)
    ·
      refine ⟨1712183212915315432307353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2282910950553753909743137 1712183212915315432307353)
      ·
        refine ⟨1284137409686486574230515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1712183212915315432307353 1284137409686486574230515)
        ·
          refine ⟨1926206114529729861345773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284137409686486574230515 1926206114529729861345773)
          ·
            refine ⟨722327292948648698004665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1926206114529729861345773 722327292948648698004665)
            ·
              refine ⟨541745469711486523503499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722327292948648698004665 541745469711486523503499)
              ·
                refine ⟨812618204567229785255249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541745469711486523503499 812618204567229785255249)
                ·
                  refine ⟨609463653425422338941437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 812618204567229785255249 609463653425422338941437)
                  ·
                    refine ⟨228548870034533377103039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609463653425422338941437 228548870034533377103039)
                    ·
                      rfl

theorem cell22_667646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_667646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667646 prefixEnd_667646 := by exact prefixLift 667646
  have htrace : WordTrace (prefixWord ++ tailWord_667646) baseStart_667646 baseEnd_667646 := by
    simpa [prefixWord, tailWord_667646, baseEnd_667646] using wordTrace_append hprefix tailTrace_667646
  have hstable : (prefixWord ++ tailWord_667646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667646).length < 2 ^ (prefixWord ++ tailWord_667646).sum := by decide
  have hdescent : baseEnd_667646 < baseStart_667646 := by decide
  rcases family_descends (prefixWord ++ tailWord_667646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667661 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_667661 : Nat := 118140960795 + 667661 * 2 ^ 59
def prefixEnd_667661 : Nat := 4983230072969 + 3 ^ 40 * 667661 * 2
def baseEnd_667661 : Nat := 228554004841078337977993

theorem tailTrace_667661 : CollatzResearch.WordTrace tailWord_667661 prefixEnd_667661 228554004841078337977993 := by
  unfold tailWord_667661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24351597234185699265722837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16234398156123799510481891 24351597234185699265722837)
  ·
    refine ⟨570740560176227326540379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 24351597234185699265722837 570740560176227326540379)
    ·
      refine ⟨856110840264340989810569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570740560176227326540379 856110840264340989810569)
      ·
        refine ⟨642083130198255742357927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 856110840264340989810569 642083130198255742357927)
        ·
          refine ⟨963124695297383613536891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642083130198255742357927 963124695297383613536891)
          ·
            refine ⟨1444687042946075420305337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963124695297383613536891 1444687042946075420305337)
            ·
              refine ⟨1083515282209556565229003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444687042946075420305337 1083515282209556565229003)
              ·
                refine ⟨1625272923314334847843505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083515282209556565229003 1625272923314334847843505)
                ·
                  refine ⟨1218954692485751135882629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1625272923314334847843505 1218954692485751135882629)
                  ·
                    refine ⟨228554004841078337977993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1218954692485751135882629 228554004841078337977993)
                    ·
                      rfl

theorem cell22_667661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_667661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667661 prefixEnd_667661 := by exact prefixLift 667661
  have htrace : WordTrace (prefixWord ++ tailWord_667661) baseStart_667661 baseEnd_667661 := by
    simpa [prefixWord, tailWord_667661, baseEnd_667661] using wordTrace_append hprefix tailTrace_667661
  have hstable : (prefixWord ++ tailWord_667661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667661).length < 2 ^ (prefixWord ++ tailWord_667661).sum := by decide
  have hdescent : baseEnd_667661 < baseStart_667661 := by decide
  rcases family_descends (prefixWord ++ tailWord_667661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667747 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 2, 3]
def baseStart_667747 : Nat := 118140960795 + 667747 * 2 ^ 59
def prefixEnd_667747 : Nat := 4983230072969 + 3 ^ 40 * 667747 * 2
def baseEnd_667747 : Nat := 228583444398602780327729

theorem tailTrace_667747 : CollatzResearch.WordTrace tailWord_667747 prefixEnd_667747 228583444398602780327729 := by
  unfold tailWord_667747
  simp only [CollatzResearch.WordTrace]
  refine ⟨24354733911874135953353495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16236489274582757302235663 24354733911874135953353495)
  ·
    refine ⟨36532100867811203930030243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24354733911874135953353495 36532100867811203930030243)
    ·
      refine ⟨54798151301716805895045365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36532100867811203930030243 54798151301716805895045365)
      ·
        refine ⟨5137326684535950552660503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54798151301716805895045365 5137326684535950552660503)
        ·
          refine ⟨7705990026803925828990755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5137326684535950552660503 7705990026803925828990755)
          ·
            refine ⟨11558985040205888743486133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7705990026803925828990755 11558985040205888743486133)
            ·
              refine ⟨1083654847519302069701825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11558985040205888743486133 1083654847519302069701825)
              ·
                refine ⟨812741135639476552276369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083654847519302069701825 812741135639476552276369)
                ·
                  refine ⟨609555851729607414207277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 812741135639476552276369 609555851729607414207277)
                  ·
                    refine ⟨228583444398602780327729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609555851729607414207277 228583444398602780327729)
                    ·
                      rfl

theorem cell22_667747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 3].length) (baseStart_667747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667747 prefixEnd_667747 := by exact prefixLift 667747
  have htrace : WordTrace (prefixWord ++ tailWord_667747) baseStart_667747 baseEnd_667747 := by
    simpa [prefixWord, tailWord_667747, baseEnd_667747] using wordTrace_append hprefix tailTrace_667747
  have hstable : (prefixWord ++ tailWord_667747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667747).length < 2 ^ (prefixWord ++ tailWord_667747).sum := by decide
  have hdescent : baseEnd_667747 < baseStart_667747 := by decide
  rcases family_descends (prefixWord ++ tailWord_667747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667803 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 3, 7]
def baseStart_667803 : Nat := 118140960795 + 667803 * 2 ^ 59
def prefixEnd_667803 : Nat := 4983230072969 + 3 ^ 40 * 667803 * 2
def baseEnd_667803 : Nat := 228602614343037300927557

theorem tailTrace_667803 : CollatzResearch.WordTrace tailWord_667803 prefixEnd_667803 228602614343037300927557 := by
  unfold tailWord_667803
  simp only [CollatzResearch.WordTrace]
  refine ⟨24356776399671257517392063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16237850933114171678261375 24356776399671257517392063)
  ·
    refine ⟨36535164599506886276088095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24356776399671257517392063 36535164599506886276088095)
    ·
      refine ⟨54802746899260329414132143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36535164599506886276088095 54802746899260329414132143)
      ·
        refine ⟨82204120348890494121198215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54802746899260329414132143 82204120348890494121198215)
        ·
          refine ⟨123306180523335741181797323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82204120348890494121198215 123306180523335741181797323)
          ·
            refine ⟨184959270785003611772695985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123306180523335741181797323 184959270785003611772695985)
            ·
              refine ⟨138719453088752708829521989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184959270785003611772695985 138719453088752708829521989)
              ·
                refine ⟨26009897454141132905535373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138719453088752708829521989 26009897454141132905535373)
                ·
                  refine ⟨9753711545302924839575765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26009897454141132905535373 9753711545302924839575765)
                  ·
                    refine ⟨228602614343037300927557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9753711545302924839575765 228602614343037300927557)
                    ·
                      rfl

theorem cell22_667803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_667803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667803 prefixEnd_667803 := by exact prefixLift 667803
  have htrace : WordTrace (prefixWord ++ tailWord_667803) baseStart_667803 baseEnd_667803 := by
    simpa [prefixWord, tailWord_667803, baseEnd_667803] using wordTrace_append hprefix tailTrace_667803
  have hstable : (prefixWord ++ tailWord_667803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667803).length < 2 ^ (prefixWord ++ tailWord_667803).sum := by decide
  have hdescent : baseEnd_667803 < baseStart_667803 := by decide
  rcases family_descends (prefixWord ++ tailWord_667803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667805 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 7]
def baseStart_667805 : Nat := 118140960795 + 667805 * 2 ^ 59
def prefixEnd_667805 : Nat := 4983230072969 + 3 ^ 40 * 667805 * 2
def baseEnd_667805 : Nat := 76201099661303320792517

theorem tailTrace_667805 : CollatzResearch.WordTrace tailWord_667805 prefixEnd_667805 76201099661303320792517 := by
  unfold tailWord_667805
  simp only [CollatzResearch.WordTrace]
  refine ⟨24356849345664011858964869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16237899563776007905976579 24356849345664011858964869)
  ·
    refine ⟨4566909252312002223555913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24356849345664011858964869 4566909252312002223555913)
    ·
      refine ⟨3425181939234001667666935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4566909252312002223555913 3425181939234001667666935)
      ·
        refine ⟨5137772908851002501500403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425181939234001667666935 5137772908851002501500403)
        ·
          refine ⟨7706659363276503752250605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5137772908851002501500403 7706659363276503752250605)
          ·
            refine ⟨2889997261228688907093977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7706659363276503752250605 2889997261228688907093977)
            ·
              refine ⟨2167497945921516680320483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2889997261228688907093977 2167497945921516680320483)
              ·
                refine ⟨3251246918882275020480725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2167497945921516680320483 3251246918882275020480725)
                ·
                  refine ⟨76201099661303320792517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3251246918882275020480725 76201099661303320792517)
                  ·
                    rfl

theorem cell22_667805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_667805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667805 prefixEnd_667805 := by exact prefixLift 667805
  have htrace : WordTrace (prefixWord ++ tailWord_667805) baseStart_667805 baseEnd_667805 := by
    simpa [prefixWord, tailWord_667805, baseEnd_667805] using wordTrace_append hprefix tailTrace_667805
  have hstable : (prefixWord ++ tailWord_667805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667805).length < 2 ^ (prefixWord ++ tailWord_667805).sum := by decide
  have hdescent : baseEnd_667805 < baseStart_667805 := by decide
  rcases family_descends (prefixWord ++ tailWord_667805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667809 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 3, 3]
def baseStart_667809 : Nat := 118140960795 + 667809 * 2 ^ 59
def prefixEnd_667809 : Nat := 4983230072969 + 3 ^ 40 * 667809 * 2
def baseEnd_667809 : Nat := 228604668265655285277539

theorem tailTrace_667809 : CollatzResearch.WordTrace tailWord_667809 prefixEnd_667809 228604668265655285277539 := by
  unfold tailWord_667809
  simp only [CollatzResearch.WordTrace]
  refine ⟨24356995237649520542110481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16237996825099680361406987 24356995237649520542110481)
  ·
    refine ⟨18267746428237140406582861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24356995237649520542110481 18267746428237140406582861)
    ·
      refine ⟨6850404910588927652468573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18267746428237140406582861 6850404910588927652468573)
      ·
        refine ⟨2568901841470847869675715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6850404910588927652468573 2568901841470847869675715)
        ·
          refine ⟨3853352762206271804513573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568901841470847869675715 3853352762206271804513573)
          ·
            refine ⟨722503642913675963346295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3853352762206271804513573 722503642913675963346295)
            ·
              refine ⟨1083755464370513945019443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722503642913675963346295 1083755464370513945019443)
              ·
                refine ⟨1625633196555770917529165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083755464370513945019443 1625633196555770917529165)
                ·
                  refine ⟨609612448708414094073437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1625633196555770917529165 609612448708414094073437)
                  ·
                    refine ⟨228604668265655285277539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609612448708414094073437 228604668265655285277539)
                    ·
                      rfl

theorem cell22_667809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_667809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667809 prefixEnd_667809 := by exact prefixLift 667809
  have htrace : WordTrace (prefixWord ++ tailWord_667809) baseStart_667809 baseEnd_667809 := by
    simpa [prefixWord, tailWord_667809, baseEnd_667809] using wordTrace_append hprefix tailTrace_667809
  have hstable : (prefixWord ++ tailWord_667809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667809).length < 2 ^ (prefixWord ++ tailWord_667809).sum := by decide
  have hdescent : baseEnd_667809 < baseStart_667809 := by decide
  rcases family_descends (prefixWord ++ tailWord_667809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667835 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 3, 4]
def baseStart_667835 : Nat := 118140960795 + 667835 * 2 ^ 59
def prefixEnd_667835 : Nat := 4983230072969 + 3 ^ 40 * 667835 * 2
def baseEnd_667835 : Nat := 228613568596999884127459

theorem tailTrace_667835 : CollatzResearch.WordTrace tailWord_667835 prefixEnd_667835 228613568596999884127459 := by
  unfold tailWord_667835
  simp only [CollatzResearch.WordTrace]
  refine ⟨24357943535555326982556959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16238629023703551321704639 24357943535555326982556959)
  ·
    refine ⟨36536915303332990473835439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24357943535555326982556959 36536915303332990473835439)
    ·
      refine ⟨54805372954999485710753159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36536915303332990473835439 54805372954999485710753159)
      ·
        refine ⟨82208059432499228566129739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54805372954999485710753159 82208059432499228566129739)
        ·
          refine ⟨123312089148748842849194609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82208059432499228566129739 123312089148748842849194609)
          ·
            refine ⟨92484066861561632136895957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123312089148748842849194609 92484066861561632136895957)
            ·
              refine ⟨2167595317067850753208499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 92484066861561632136895957 2167595317067850753208499)
              ·
                refine ⟨3251392975601776129812749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2167595317067850753208499 3251392975601776129812749)
                ·
                  refine ⟨1219272365850666048679781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3251392975601776129812749 1219272365850666048679781)
                  ·
                    refine ⟨228613568596999884127459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1219272365850666048679781 228613568596999884127459)
                    ·
                      rfl

theorem cell22_667835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 4].length) (baseStart_667835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667835 prefixEnd_667835 := by exact prefixLift 667835
  have htrace : WordTrace (prefixWord ++ tailWord_667835) baseStart_667835 baseEnd_667835 := by
    simpa [prefixWord, tailWord_667835, baseEnd_667835] using wordTrace_append hprefix tailTrace_667835
  have hstable : (prefixWord ++ tailWord_667835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667835).length < 2 ^ (prefixWord ++ tailWord_667835).sum := by decide
  have hdescent : baseEnd_667835 < baseStart_667835 := by decide
  rcases family_descends (prefixWord ++ tailWord_667835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667882 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_667882 : Nat := 118140960795 + 667882 * 2 ^ 59
def prefixEnd_667882 : Nat := 4983230072969 + 3 ^ 40 * 667882 * 2
def baseEnd_667882 : Nat := 228629657657507428202315

theorem tailTrace_667882 : CollatzResearch.WordTrace tailWord_667882 prefixEnd_667882 228629657657507428202315 := by
  unfold tailWord_667882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089914441596263502379475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16239771844256702673011933 6089914441596263502379475)
  ·
    refine ⟨9134871662394395253569213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089914441596263502379475 9134871662394395253569213)
    ·
      refine ⟨3425576873397898220088455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9134871662394395253569213 3425576873397898220088455)
      ·
        refine ⟨5138365310096847330132683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425576873397898220088455 5138365310096847330132683)
        ·
          refine ⟨7707547965145270995199025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5138365310096847330132683 7707547965145270995199025)
          ·
            refine ⟨5780660973858953246399269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7707547965145270995199025 5780660973858953246399269)
            ·
              refine ⟨1083873932598553733699863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5780660973858953246399269 1083873932598553733699863)
              ·
                refine ⟨1625810898897830600549795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083873932598553733699863 1625810898897830600549795)
                ·
                  refine ⟨2438716348346745900824693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625810898897830600549795 2438716348346745900824693)
                  ·
                    refine ⟨228629657657507428202315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2438716348346745900824693 228629657657507428202315)
                    ·
                      rfl

theorem cell22_667882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_667882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667882 prefixEnd_667882 := by exact prefixLift 667882
  have htrace : WordTrace (prefixWord ++ tailWord_667882) baseStart_667882 baseEnd_667882 := by
    simpa [prefixWord, tailWord_667882, baseEnd_667882] using wordTrace_append hprefix tailTrace_667882
  have hstable : (prefixWord ++ tailWord_667882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667882).length < 2 ^ (prefixWord ++ tailWord_667882).sum := by decide
  have hdescent : baseEnd_667882 < baseStart_667882 := by decide
  rcases family_descends (prefixWord ++ tailWord_667882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667925 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_667925 : Nat := 118140960795 + 667925 * 2 ^ 59
def prefixEnd_667925 : Nat := 4983230072969 + 3 ^ 40 * 667925 * 2
def baseEnd_667925 : Nat := 228644377436269649377183

theorem tailTrace_667925 : CollatzResearch.WordTrace tailWord_667925 prefixEnd_667925 228644377436269649377183 := by
  unfold tailWord_667925
  simp only [CollatzResearch.WordTrace]
  refine ⟨24361226105229272353333229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16240817403486181568888819 24361226105229272353333229)
  ·
    refine ⟨9135459789460977132499961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24361226105229272353333229 9135459789460977132499961)
    ·
      refine ⟨6851594842095732849374971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9135459789460977132499961 6851594842095732849374971)
      ·
        refine ⟨10277392263143599274062457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6851594842095732849374971 10277392263143599274062457)
        ·
          refine ⟨7708044197357699455546843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10277392263143599274062457 7708044197357699455546843)
          ·
            refine ⟨11562066296036549183320265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7708044197357699455546843 11562066296036549183320265)
            ·
              refine ⟨8671549722027411887490199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11562066296036549183320265 8671549722027411887490199)
              ·
                refine ⟨13007324583041117831235299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8671549722027411887490199 13007324583041117831235299)
                ·
                  refine ⟨19510986874561676746852949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13007324583041117831235299 19510986874561676746852949)
                  ·
                    refine ⟨228644377436269649377183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19510986874561676746852949 228644377436269649377183)
                    ·
                      rfl

theorem cell22_667925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_667925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667925 prefixEnd_667925 := by exact prefixLift 667925
  have htrace : WordTrace (prefixWord ++ tailWord_667925) baseStart_667925 baseEnd_667925 := by
    simpa [prefixWord, tailWord_667925, baseEnd_667925] using wordTrace_append hprefix tailTrace_667925
  have hstable : (prefixWord ++ tailWord_667925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667925).length < 2 ^ (prefixWord ++ tailWord_667925).sum := by decide
  have hdescent : baseEnd_667925 < baseStart_667925 := by decide
  rcases family_descends (prefixWord ++ tailWord_667925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667933 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_667933 : Nat := 118140960795 + 667933 * 2 ^ 59
def prefixEnd_667933 : Nat := 4983230072969 + 3 ^ 40 * 667933 * 2
def baseEnd_667933 : Nat := 228647115999760295177159

theorem tailTrace_667933 : CollatzResearch.WordTrace tailWord_667933 prefixEnd_667933 228647115999760295177159 := by
  unfold tailWord_667933
  simp only [CollatzResearch.WordTrace]
  refine ⟨24361517889200289719624453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16241011926133526479749635 24361517889200289719624453)
  ·
    refine ⟨4567784604225054322429585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24361517889200289719624453 4567784604225054322429585)
    ·
      refine ⟨3425838453168790741822189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4567784604225054322429585 3425838453168790741822189)
      ·
        refine ⟨1284689419938296528183321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3425838453168790741822189 1284689419938296528183321)
        ·
          refine ⟨963517064953722396137491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284689419938296528183321 963517064953722396137491)
          ·
            refine ⟨1445275597430583594206237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963517064953722396137491 1445275597430583594206237)
            ·
              refine ⟨541978349036468847827339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1445275597430583594206237 541978349036468847827339)
              ·
                refine ⟨812967523554703271741009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541978349036468847827339 812967523554703271741009)
                ·
                  refine ⟨609725642666027453805757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 812967523554703271741009 609725642666027453805757)
                  ·
                    refine ⟨228647115999760295177159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609725642666027453805757 228647115999760295177159)
                    ·
                      rfl

theorem cell22_667933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_667933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667933 prefixEnd_667933 := by exact prefixLift 667933
  have htrace : WordTrace (prefixWord ++ tailWord_667933) baseStart_667933 baseEnd_667933 := by
    simpa [prefixWord, tailWord_667933, baseEnd_667933] using wordTrace_append hprefix tailTrace_667933
  have hstable : (prefixWord ++ tailWord_667933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667933).length < 2 ^ (prefixWord ++ tailWord_667933).sum := by decide
  have hdescent : baseEnd_667933 < baseStart_667933 := by decide
  rcases family_descends (prefixWord ++ tailWord_667933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667946 : List Nat := [3, 1, 4, 2, 2, 2, 2, 6]
def baseStart_667946 : Nat := 118140960795 + 667946 * 2 ^ 59
def prefixEnd_667946 : Nat := 4983230072969 + 3 ^ 40 * 667946 * 2
def baseEnd_667946 : Nat := 25405729573936954955791

theorem tailTrace_667946 : CollatzResearch.WordTrace tailWord_667946 prefixEnd_667946 25405729573936954955791 := by
  unfold tailWord_667946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6090498009538298234961923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16241328025435461959898461 6090498009538298234961923)
  ·
    refine ⟨9135747014307447352442885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6090498009538298234961923 9135747014307447352442885)
    ·
      refine ⟨1712952565182646378583041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9135747014307447352442885 1712952565182646378583041)
      ·
        refine ⟨1284714423886984783937281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1712952565182646378583041 1284714423886984783937281)
        ·
          refine ⟨963535817915238587952961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284714423886984783937281 963535817915238587952961)
          ·
            refine ⟨722651863436428940964721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963535817915238587952961 722651863436428940964721)
            ·
              refine ⟨541988897577321705723541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722651863436428940964721 541988897577321705723541)
              ·
                refine ⟨25405729573936954955791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 541988897577321705723541 25405729573936954955791)
                ·
                  rfl

theorem cell22_667946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_667946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_667946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_667946 prefixEnd_667946 := by exact prefixLift 667946
  have htrace : WordTrace (prefixWord ++ tailWord_667946) baseStart_667946 baseEnd_667946 := by
    simpa [prefixWord, tailWord_667946, baseEnd_667946] using wordTrace_append hprefix tailTrace_667946
  have hstable : (prefixWord ++ tailWord_667946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667946).length < 2 ^ (prefixWord ++ tailWord_667946).sum := by decide
  have hdescent : baseEnd_667946 < baseStart_667946 := by decide
  rcases family_descends (prefixWord ++ tailWord_667946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668064 : List Nat := [2, 1, 1, 4, 1, 4, 3, 6]
def baseStart_668064 : Nat := 118140960795 + 668064 * 2 ^ 59
def prefixEnd_668064 : Nat := 4983230072969 + 3 ^ 40 * 668064 * 2
def baseEnd_668064 : Nat := 25410217775213291127973

theorem tailTrace_668064 : CollatzResearch.WordTrace tailWord_668064 prefixEnd_668064 25410217775213291127973 := by
  unfold tailWord_668064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12183147925862849546321623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16244197234483799395095497 12183147925862849546321623)
  ·
    refine ⟨18274721888794274319482435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12183147925862849546321623 18274721888794274319482435)
    ·
      refine ⟨27412082833191411479223653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18274721888794274319482435 27412082833191411479223653)
      ·
        refine ⟨5139765531223389652354435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27412082833191411479223653 5139765531223389652354435)
        ·
          refine ⟨7709648296835084478531653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5139765531223389652354435 7709648296835084478531653)
          ·
            refine ⟨1445559055656578339724685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7709648296835084478531653 1445559055656578339724685)
            ·
              refine ⟨542084645871216877396757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1445559055656578339724685 542084645871216877396757)
              ·
                refine ⟨25410217775213291127973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 542084645871216877396757 25410217775213291127973)
                ·
                  rfl

theorem cell22_668064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 6].length) (baseStart_668064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668064 prefixEnd_668064 := by exact prefixLift 668064
  have htrace : WordTrace (prefixWord ++ tailWord_668064) baseStart_668064 baseEnd_668064 := by
    simpa [prefixWord, tailWord_668064, baseEnd_668064] using wordTrace_append hprefix tailTrace_668064
  have hstable : (prefixWord ++ tailWord_668064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668064).length < 2 ^ (prefixWord ++ tailWord_668064).sum := by decide
  have hdescent : baseEnd_668064 < baseStart_668064 := by decide
  rcases family_descends (prefixWord ++ tailWord_668064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668085 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_668085 : Nat := 118140960795 + 668085 * 2 ^ 59
def prefixEnd_668085 : Nat := 4983230072969 + 3 ^ 40 * 668085 * 2
def baseEnd_668085 : Nat := 228699148706082565376693

theorem tailTrace_668085 : CollatzResearch.WordTrace tailWord_668085 prefixEnd_668085 228699148706082565376693 := by
  unfold tailWord_668085
  simp only [CollatzResearch.WordTrace]
  refine ⟨24367061784649619679157709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16244707856433079786105139 24367061784649619679157709)
  ·
    refine ⟨9137648169243607379684141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24367061784649619679157709 9137648169243607379684141)
    ·
      refine ⟨3426618063466352767381553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9137648169243607379684141 3426618063466352767381553)
      ·
        refine ⟨2569963547599764575536165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3426618063466352767381553 2569963547599764575536165)
        ·
          refine ⟨481868165174955857913031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2569963547599764575536165 481868165174955857913031)
          ·
            refine ⟨722802247762433786869547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481868165174955857913031 722802247762433786869547)
            ·
              refine ⟨1084203371643650680304321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722802247762433786869547 1084203371643650680304321)
              ·
                refine ⟨813152528732738010228241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084203371643650680304321 813152528732738010228241)
                ·
                  refine ⟨609864396549553507671181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813152528732738010228241 609864396549553507671181)
                  ·
                    refine ⟨228699148706082565376693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609864396549553507671181 228699148706082565376693)
                    ·
                      rfl

theorem cell22_668085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_668085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668085 prefixEnd_668085 := by exact prefixLift 668085
  have htrace : WordTrace (prefixWord ++ tailWord_668085) baseStart_668085 baseEnd_668085 := by
    simpa [prefixWord, tailWord_668085, baseEnd_668085] using wordTrace_append hprefix tailTrace_668085
  have hstable : (prefixWord ++ tailWord_668085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668085).length < 2 ^ (prefixWord ++ tailWord_668085).sum := by decide
  have hdescent : baseEnd_668085 < baseStart_668085 := by decide
  rcases family_descends (prefixWord ++ tailWord_668085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668139 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 1, 4]
def baseStart_668139 : Nat := 118140960795 + 668139 * 2 ^ 59
def prefixEnd_668139 : Nat := 4983230072969 + 3 ^ 40 * 668139 * 2
def baseEnd_668139 : Nat := 228717634009644424526527

theorem tailTrace_668139 : CollatzResearch.WordTrace tailWord_668139 prefixEnd_668139 228717634009644424526527 := by
  unfold tailWord_668139
  simp only [CollatzResearch.WordTrace]
  refine ⟨24369031326453986901623471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16246020884302657934415647 24369031326453986901623471)
  ·
    refine ⟨36553546989680980352435207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24369031326453986901623471 36553546989680980352435207)
    ·
      refine ⟨54830320484521470528652811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36553546989680980352435207 54830320484521470528652811)
      ·
        refine ⟨82245480726782205792979217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54830320484521470528652811 82245480726782205792979217)
        ·
          refine ⟨61684110545086654344734413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82245480726782205792979217 61684110545086654344734413)
          ·
            refine ⟨23131541454407495379275405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61684110545086654344734413 23131541454407495379275405)
            ·
              refine ⟨8674328045402810767228277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23131541454407495379275405 8674328045402810767228277)
              ·
                refine ⟨813218254256513509427651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8674328045402810767228277 813218254256513509427651)
                ·
                  refine ⟨1219827381384770264141477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813218254256513509427651 1219827381384770264141477)
                  ·
                    refine ⟨228717634009644424526527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1219827381384770264141477 228717634009644424526527)
                    ·
                      rfl

theorem cell22_668139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 4].length) (baseStart_668139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668139 prefixEnd_668139 := by exact prefixLift 668139
  have htrace : WordTrace (prefixWord ++ tailWord_668139) baseStart_668139 baseEnd_668139 := by
    simpa [prefixWord, tailWord_668139, baseEnd_668139] using wordTrace_append hprefix tailTrace_668139
  have hstable : (prefixWord ++ tailWord_668139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668139).length < 2 ^ (prefixWord ++ tailWord_668139).sum := by decide
  have hdescent : baseEnd_668139 < baseStart_668139 := by decide
  rcases family_descends (prefixWord ++ tailWord_668139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668169 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 6, 3]
def baseStart_668169 : Nat := 118140960795 + 668169 * 2 ^ 59
def prefixEnd_668169 : Nat := 4983230072969 + 3 ^ 40 * 668169 * 2
def baseEnd_668169 : Nat := 228727903622734346276435

theorem tailTrace_668169 : CollatzResearch.WordTrace tailWord_668169 prefixEnd_668169 228727903622734346276435 := by
  unfold tailWord_668169
  simp only [CollatzResearch.WordTrace]
  refine ⟨24370125516345302025215561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16246750344230201350143707 24370125516345302025215561)
  ·
    refine ⟨18277594137258976518911671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24370125516345302025215561 18277594137258976518911671)
    ·
      refine ⟨27416391205888464778367507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18277594137258976518911671 27416391205888464778367507)
      ·
        refine ⟨41124586808832697167551261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27416391205888464778367507 41124586808832697167551261)
        ·
          refine ⟨15421720053312261437831723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41124586808832697167551261 15421720053312261437831723)
          ·
            refine ⟨23132580079968392156747585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15421720053312261437831723 23132580079968392156747585)
            ·
              refine ⟨17349435059976294117560689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23132580079968392156747585 17349435059976294117560689)
              ·
                refine ⟨13012076294982220588170517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17349435059976294117560689 13012076294982220588170517)
                ·
                  refine ⟨609941076327291590070493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13012076294982220588170517 609941076327291590070493)
                  ·
                    refine ⟨228727903622734346276435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609941076327291590070493 228727903622734346276435)
                    ·
                      rfl

theorem cell22_668169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_668169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668169 prefixEnd_668169 := by exact prefixLift 668169
  have htrace : WordTrace (prefixWord ++ tailWord_668169) baseStart_668169 baseEnd_668169 := by
    simpa [prefixWord, tailWord_668169, baseEnd_668169] using wordTrace_append hprefix tailTrace_668169
  have hstable : (prefixWord ++ tailWord_668169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668169).length < 2 ^ (prefixWord ++ tailWord_668169).sum := by decide
  have hdescent : baseEnd_668169 < baseStart_668169 := by decide
  rcases family_descends (prefixWord ++ tailWord_668169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668231 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 5, 3]
def baseStart_668231 : Nat := 118140960795 + 668231 * 2 ^ 59
def prefixEnd_668231 : Nat := 4983230072969 + 3 ^ 40 * 668231 * 2
def baseEnd_668231 : Nat := 228749127489786851226245

theorem tailTrace_668231 : CollatzResearch.WordTrace tailWord_668231 prefixEnd_668231 228749127489786851226245 := by
  unfold tailWord_668231
  simp only [CollatzResearch.WordTrace]
  refine ⟨24372386842120686613972547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16248257894747124409315031 24372386842120686613972547)
  ·
    refine ⟨36558580263181029920958821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24372386842120686613972547 36558580263181029920958821)
    ·
      refine ⟨6854733799346443110179779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36558580263181029920958821 6854733799346443110179779)
      ·
        refine ⟨10282100699019664665269669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6854733799346443110179779 10282100699019664665269669)
        ·
          refine ⟨1927893881066187124738063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10282100699019664665269669 1927893881066187124738063)
          ·
            refine ⟨2891840821599280687107095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927893881066187124738063 2891840821599280687107095)
            ·
              refine ⟨4337761232398921030660643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891840821599280687107095 4337761232398921030660643)
              ·
                refine ⟨6506641848598381545990965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337761232398921030660643 6506641848598381545990965)
                ·
                  refine ⟨609997673306098269936653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6506641848598381545990965 609997673306098269936653)
                  ·
                    refine ⟨228749127489786851226245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 609997673306098269936653 228749127489786851226245)
                    ·
                      rfl

theorem cell22_668231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_668231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668231 prefixEnd_668231 := by exact prefixLift 668231
  have htrace : WordTrace (prefixWord ++ tailWord_668231) baseStart_668231 baseEnd_668231 := by
    simpa [prefixWord, tailWord_668231, baseEnd_668231] using wordTrace_append hprefix tailTrace_668231
  have hstable : (prefixWord ++ tailWord_668231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668231).length < 2 ^ (prefixWord ++ tailWord_668231).sum := by decide
  have hdescent : baseEnd_668231 < baseStart_668231 := by decide
  rcases family_descends (prefixWord ++ tailWord_668231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668248 : List Nat := [2, 1, 2, 2, 1, 2, 3, 5, 1, 3]
def baseStart_668248 : Nat := 118140960795 + 668248 * 2 ^ 59
def prefixEnd_668248 : Nat := 4983230072969 + 3 ^ 40 * 668248 * 2
def baseEnd_668248 : Nat := 228754946937204473551193

theorem tailTrace_668248 : CollatzResearch.WordTrace tailWord_668248 prefixEnd_668248 228754946937204473551193 := by
  unfold tailWord_668248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12186503441529549258670699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16248671255372732344894265 12186503441529549258670699)
  ·
    refine ⟨18279755162294323888006049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12186503441529549258670699 18279755162294323888006049)
    ·
      refine ⟨13709816371720742916004537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18279755162294323888006049 13709816371720742916004537)
      ·
        refine ⟨10282362278790557187003403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13709816371720742916004537 10282362278790557187003403)
        ·
          refine ⟨15423543418185835780505105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10282362278790557187003403 15423543418185835780505105)
          ·
            refine ⟨11567657563639376835378829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15423543418185835780505105 11567657563639376835378829)
            ·
              refine ⟨4337871586364766313267061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11567657563639376835378829 4337871586364766313267061)
              ·
                refine ⟨406675461221696841868787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4337871586364766313267061 406675461221696841868787)
                ·
                  refine ⟨610013191832545262803181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406675461221696841868787 610013191832545262803181)
                  ·
                    refine ⟨228754946937204473551193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 610013191832545262803181 228754946937204473551193)
                    ·
                      rfl

theorem cell22_668248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_668248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668248 prefixEnd_668248 := by exact prefixLift 668248
  have htrace : WordTrace (prefixWord ++ tailWord_668248) baseStart_668248 baseEnd_668248 := by
    simpa [prefixWord, tailWord_668248, baseEnd_668248] using wordTrace_append hprefix tailTrace_668248
  have hstable : (prefixWord ++ tailWord_668248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668248).length < 2 ^ (prefixWord ++ tailWord_668248).sum := by decide
  have hdescent : baseEnd_668248 < baseStart_668248 := by decide
  rcases family_descends (prefixWord ++ tailWord_668248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668259 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 4, 5]
def baseStart_668259 : Nat := 118140960795 + 668259 * 2 ^ 59
def prefixEnd_668259 : Nat := 4983230072969 + 3 ^ 40 * 668259 * 2
def baseEnd_668259 : Nat := 228758712462004111526159

theorem tailTrace_668259 : CollatzResearch.WordTrace tailWord_668259 prefixEnd_668259 228758712462004111526159 := by
  unfold tailWord_668259
  simp only [CollatzResearch.WordTrace]
  refine ⟨24373408086019247395991831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16248938724012831597327887 24373408086019247395991831)
  ·
    refine ⟨36560112129028871093987747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24373408086019247395991831 36560112129028871093987747)
    ·
      refine ⟨54840168193543306640981621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36560112129028871093987747 54840168193543306640981621)
      ·
        refine ⟨5141265768144684997592027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54840168193543306640981621 5141265768144684997592027)
        ·
          refine ⟨7711898652217027496388041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5141265768144684997592027 7711898652217027496388041)
          ·
            refine ⟨5783923989162770622291031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711898652217027496388041 5783923989162770622291031)
            ·
              refine ⟨8675885983744155933436547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783923989162770622291031 8675885983744155933436547)
              ·
                refine ⟨13013828975616233900154821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675885983744155933436547 13013828975616233900154821)
                ·
                  refine ⟨2440092932928043856279029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13013828975616233900154821 2440092932928043856279029)
                  ·
                    refine ⟨228758712462004111526159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2440092932928043856279029 228758712462004111526159)
                    ·
                      rfl

theorem cell22_668259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_668259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668259 prefixEnd_668259 := by exact prefixLift 668259
  have htrace : WordTrace (prefixWord ++ tailWord_668259) baseStart_668259 baseEnd_668259 := by
    simpa [prefixWord, tailWord_668259, baseEnd_668259] using wordTrace_append hprefix tailTrace_668259
  have hstable : (prefixWord ++ tailWord_668259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668259).length < 2 ^ (prefixWord ++ tailWord_668259).sum := by decide
  have hdescent : baseEnd_668259 < baseStart_668259 := by decide
  rcases family_descends (prefixWord ++ tailWord_668259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668261 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 7]
def baseStart_668261 : Nat := 118140960795 + 668261 * 2 ^ 59
def prefixEnd_668261 : Nat := 4983230072969 + 3 ^ 40 * 668261 * 2
def baseEnd_668261 : Nat := 76253132367625590992051

theorem tailTrace_668261 : CollatzResearch.WordTrace tailWord_668261 prefixEnd_668261 76253132367625590992051 := by
  unfold tailWord_668261
  simp only [CollatzResearch.WordTrace]
  refine ⟨24373481032012001737564637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16248987354674667825043091 24373481032012001737564637)
  ·
    refine ⟨9140055387004500651586739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24373481032012001737564637 9140055387004500651586739)
    ·
      refine ⟨13710083080506750977380109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9140055387004500651586739 13710083080506750977380109)
      ·
        refine ⟨5141281155190031616517541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13710083080506750977380109 5141281155190031616517541)
        ·
          refine ⟨963990216598130928097039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5141281155190031616517541 963990216598130928097039)
          ·
            refine ⟨1445985324897196392145559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963990216598130928097039 1445985324897196392145559)
            ·
              refine ⟨2168977987345794588218339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445985324897196392145559 2168977987345794588218339)
              ·
                refine ⟨3253466981018691882327509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2168977987345794588218339 3253466981018691882327509)
                ·
                  refine ⟨76253132367625590992051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3253466981018691882327509 76253132367625590992051)
                  ·
                    rfl

theorem cell22_668261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_668261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668261 prefixEnd_668261 := by exact prefixLift 668261
  have htrace : WordTrace (prefixWord ++ tailWord_668261) baseStart_668261 baseEnd_668261 := by
    simpa [prefixWord, tailWord_668261, baseEnd_668261] using wordTrace_append hprefix tailTrace_668261
  have hstable : (prefixWord ++ tailWord_668261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668261).length < 2 ^ (prefixWord ++ tailWord_668261).sum := by decide
  have hdescent : baseEnd_668261 < baseStart_668261 := by decide
  rcases family_descends (prefixWord ++ tailWord_668261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668291 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 1, 4]
def baseStart_668291 : Nat := 118140960795 + 668291 * 2 ^ 59
def prefixEnd_668291 : Nat := 4983230072969 + 3 ^ 40 * 668291 * 2
def baseEnd_668291 : Nat := 228769666715966694726061

theorem tailTrace_668291 : CollatzResearch.WordTrace tailWord_668291 prefixEnd_668291 228769666715966694726061 := by
  unfold tailWord_668291
  simp only [CollatzResearch.WordTrace]
  refine ⟨24374575221903316861156727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16249716814602211240771151 24374575221903316861156727)
  ·
    refine ⟨36561862832854975291735091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24374575221903316861156727 36561862832854975291735091)
    ·
      refine ⟨54842794249282462937602637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36561862832854975291735091 54842794249282462937602637)
      ·
        refine ⟨20566047843480923601600989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54842794249282462937602637 20566047843480923601600989)
        ·
          refine ⟨7712267941305346350600371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20566047843480923601600989 7712267941305346350600371)
          ·
            refine ⟨11568401911958019525900557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7712267941305346350600371 11568401911958019525900557)
            ·
              refine ⟨4338150716984257322212709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11568401911958019525900557 4338150716984257322212709)
              ·
                refine ⟨813403259434548247914883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4338150716984257322212709 813403259434548247914883)
                ·
                  refine ⟨1220104889151822371872325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813403259434548247914883 1220104889151822371872325)
                  ·
                    refine ⟨228769666715966694726061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1220104889151822371872325 228769666715966694726061)
                    ·
                      rfl

theorem cell22_668291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 4].length) (baseStart_668291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668291 prefixEnd_668291 := by exact prefixLift 668291
  have htrace : WordTrace (prefixWord ++ tailWord_668291) baseStart_668291 baseEnd_668291 := by
    simpa [prefixWord, tailWord_668291, baseEnd_668291] using wordTrace_append hprefix tailTrace_668291
  have hstable : (prefixWord ++ tailWord_668291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668291).length < 2 ^ (prefixWord ++ tailWord_668291).sum := by decide
  have hdescent : baseEnd_668291 < baseStart_668291 := by decide
  rcases family_descends (prefixWord ++ tailWord_668291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668372 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_668372 : Nat := 118140960795 + 668372 * 2 ^ 59
def prefixEnd_668372 : Nat := 4983230072969 + 3 ^ 40 * 668372 * 2
def baseEnd_668372 : Nat := 228797394671309483450813

theorem tailTrace_668372 : CollatzResearch.WordTrace tailWord_668372 prefixEnd_668372 228797394671309483450813 := by
  unfold tailWord_668372
  simp only [CollatzResearch.WordTrace]
  refine ⟨12188764767304933847427685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16251686356406578463236913 12188764767304933847427685)
  ·
    refine ⟨2285393393869675096392691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12188764767304933847427685 2285393393869675096392691)
    ·
      refine ⟨3428090090804512644589037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2285393393869675096392691 3428090090804512644589037)
      ·
        refine ⟨1285533784051692241720889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3428090090804512644589037 1285533784051692241720889)
        ·
          refine ⟨964150338038769181290667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1285533784051692241720889 964150338038769181290667)
          ·
            refine ⟨1446225507058153771936001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964150338038769181290667 1446225507058153771936001)
            ·
              refine ⟨1084669130293615328952001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446225507058153771936001 1084669130293615328952001)
              ·
                refine ⟨813501847720211496714001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084669130293615328952001 813501847720211496714001)
                ·
                  refine ⟨610126385790158622535501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813501847720211496714001 610126385790158622535501)
                  ·
                    refine ⟨228797394671309483450813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 610126385790158622535501 228797394671309483450813)
                    ·
                      rfl

theorem cell22_668372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_668372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668372 prefixEnd_668372 := by exact prefixLift 668372
  have htrace : WordTrace (prefixWord ++ tailWord_668372) baseStart_668372 baseEnd_668372 := by
    simpa [prefixWord, tailWord_668372, baseEnd_668372] using wordTrace_append hprefix tailTrace_668372
  have hstable : (prefixWord ++ tailWord_668372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668372).length < 2 ^ (prefixWord ++ tailWord_668372).sum := by decide
  have hdescent : baseEnd_668372 < baseStart_668372 := by decide
  rcases family_descends (prefixWord ++ tailWord_668372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668404 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_668404 : Nat := 118140960795 + 668404 * 2 ^ 59
def prefixEnd_668404 : Nat := 4983230072969 + 3 ^ 40 * 668404 * 2
def baseEnd_668404 : Nat := 228808348925272066650715

theorem tailTrace_668404 : CollatzResearch.WordTrace tailWord_668404 prefixEnd_668404 228808348925272066650715 := by
  unfold tailWord_668404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12189348335246968580010133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16252464446995958106680177 12189348335246968580010133)
  ·
    refine ⟨571375703214701652187975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12189348335246968580010133 571375703214701652187975)
    ·
      refine ⟨857063554822052478281963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571375703214701652187975 857063554822052478281963)
      ·
        refine ⟨1285595332233078717422945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857063554822052478281963 1285595332233078717422945)
        ·
          refine ⟨964196499174809038067209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1285595332233078717422945 964196499174809038067209)
          ·
            refine ⟨723147374381106778550407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964196499174809038067209 723147374381106778550407)
            ·
              refine ⟨1084721061571660167825611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723147374381106778550407 1084721061571660167825611)
              ·
                refine ⟨1627081592357490251738417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084721061571660167825611 1627081592357490251738417)
                ·
                  refine ⟨1220311194268117688803813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1627081592357490251738417 1220311194268117688803813)
                  ·
                    refine ⟨228808348925272066650715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1220311194268117688803813 228808348925272066650715)
                    ·
                      rfl

theorem cell22_668404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_668404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668404 prefixEnd_668404 := by exact prefixLift 668404
  have htrace : WordTrace (prefixWord ++ tailWord_668404) baseStart_668404 baseEnd_668404 := by
    simpa [prefixWord, tailWord_668404, baseEnd_668404] using wordTrace_append hprefix tailTrace_668404
  have hstable : (prefixWord ++ tailWord_668404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668404).length < 2 ^ (prefixWord ++ tailWord_668404).sum := by decide
  have hdescent : baseEnd_668404 < baseStart_668404 := by decide
  rcases family_descends (prefixWord ++ tailWord_668404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668471 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 1, 6]
def baseStart_668471 : Nat := 118140960795 + 668471 * 2 ^ 59
def prefixEnd_668471 : Nat := 4983230072969 + 3 ^ 40 * 668471 * 2
def baseEnd_668471 : Nat := 228831284394506225225509

theorem tailTrace_668471 : CollatzResearch.WordTrace tailWord_668471 prefixEnd_668471 228831284394506225225509 := by
  unfold tailWord_668471
  simp only [CollatzResearch.WordTrace]
  refine ⟨24381140361251207602709267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16254093574167471735139511 24381140361251207602709267)
  ·
    refine ⟨36571710541876811404063901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24381140361251207602709267 36571710541876811404063901)
    ·
      refine ⟨13714391453203804276523963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36571710541876811404063901 13714391453203804276523963)
      ·
        refine ⟨20571587179805706414785945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13714391453203804276523963 20571587179805706414785945)
        ·
          refine ⟨15428690384854279811089459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20571587179805706414785945 15428690384854279811089459)
          ·
            refine ⟨23143035577281419716634189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15428690384854279811089459 23143035577281419716634189)
            ·
              refine ⟨8678638341480532393737821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23143035577281419716634189 8678638341480532393737821)
              ·
                refine ⟨3254489378055199647651683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8678638341480532393737821 3254489378055199647651683)
                ·
                  refine ⟨4881734067082799471477525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254489378055199647651683 4881734067082799471477525)
                  ·
                    refine ⟨228831284394506225225509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4881734067082799471477525 228831284394506225225509)
                    ·
                      rfl

theorem cell22_668471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_668471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668471 prefixEnd_668471 := by exact prefixLift 668471
  have htrace : WordTrace (prefixWord ++ tailWord_668471) baseStart_668471 baseEnd_668471 := by
    simpa [prefixWord, tailWord_668471, baseEnd_668471] using wordTrace_append hprefix tailTrace_668471
  have hstable : (prefixWord ++ tailWord_668471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668471).length < 2 ^ (prefixWord ++ tailWord_668471).sum := by decide
  have hdescent : baseEnd_668471 < baseStart_668471 := by decide
  rcases family_descends (prefixWord ++ tailWord_668471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668488 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_668488 : Nat := 118140960795 + 668488 * 2 ^ 59
def prefixEnd_668488 : Nat := 4983230072969 + 3 ^ 40 * 668488 * 2
def baseEnd_668488 : Nat := 228837103841923847550457

theorem tailTrace_668488 : CollatzResearch.WordTrace tailWord_668488 prefixEnd_668488 228837103841923847550457 := by
  unfold tailWord_668488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12190880201094809753039059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16254506934793079670718745 12190880201094809753039059)
  ·
    refine ⟨18286320301642214629558589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12190880201094809753039059 18286320301642214629558589)
    ·
      refine ⟨6857370113115830486084471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18286320301642214629558589 6857370113115830486084471)
      ·
        refine ⟨10286055169673745729126707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857370113115830486084471 10286055169673745729126707)
        ·
          refine ⟨15429082754510618593690061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10286055169673745729126707 15429082754510618593690061)
          ·
            refine ⟨5785906032941481972633773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15429082754510618593690061 5785906032941481972633773)
            ·
              refine ⟨2169714762353055739737665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5785906032941481972633773 2169714762353055739737665)
              ·
                refine ⟨1627286071764791804803249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169714762353055739737665 1627286071764791804803249)
                ·
                  refine ⟨1220464553823593853602437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1627286071764791804803249 1220464553823593853602437)
                  ·
                    refine ⟨228837103841923847550457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1220464553823593853602437 228837103841923847550457)
                    ·
                      rfl

theorem cell22_668488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_668488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668488 prefixEnd_668488 := by exact prefixLift 668488
  have htrace : WordTrace (prefixWord ++ tailWord_668488) baseStart_668488 baseEnd_668488 := by
    simpa [prefixWord, tailWord_668488, baseEnd_668488] using wordTrace_append hprefix tailTrace_668488
  have hstable : (prefixWord ++ tailWord_668488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668488).length < 2 ^ (prefixWord ++ tailWord_668488).sum := by decide
  have hdescent : baseEnd_668488 < baseStart_668488 := by decide
  rcases family_descends (prefixWord ++ tailWord_668488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668492 : List Nat := [2, 2, 1, 3, 3, 2, 3, 2, 4]
def baseStart_668492 : Nat := 118140960795 + 668492 * 2 ^ 59
def prefixEnd_668492 : Nat := 4983230072969 + 3 ^ 40 * 668492 * 2
def baseEnd_668492 : Nat := 76279491041223056816815

theorem tailTrace_668492 : CollatzResearch.WordTrace tailWord_668492 prefixEnd_668492 76279491041223056816815 := by
  unfold tailWord_668492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12190953147087564094611865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16254604196116752126149153 12190953147087564094611865)
  ·
    refine ⟨9143214860315673070958899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12190953147087564094611865 9143214860315673070958899)
    ·
      refine ⟨13714822290473509606438349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9143214860315673070958899 13714822290473509606438349)
      ·
        refine ⟨5143058358927566102414381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13714822290473509606438349 5143058358927566102414381)
        ·
          refine ⟨1928646884597837288405393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5143058358927566102414381 1928646884597837288405393)
          ·
            refine ⟨1446485163448377966304045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928646884597837288405393 1446485163448377966304045)
            ·
              refine ⟨542431936293141737364017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1446485163448377966304045 542431936293141737364017)
              ·
                refine ⟨406823952219856303023013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542431936293141737364017 406823952219856303023013)
                ·
                  refine ⟨76279491041223056816815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406823952219856303023013 76279491041223056816815)
                  ·
                    rfl

theorem cell22_668492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_668492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668492 prefixEnd_668492 := by exact prefixLift 668492
  have htrace : WordTrace (prefixWord ++ tailWord_668492) baseStart_668492 baseEnd_668492 := by
    simpa [prefixWord, tailWord_668492, baseEnd_668492] using wordTrace_append hprefix tailTrace_668492
  have hstable : (prefixWord ++ tailWord_668492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668492).length < 2 ^ (prefixWord ++ tailWord_668492).sum := by decide
  have hdescent : baseEnd_668492 < baseStart_668492 := by decide
  rcases family_descends (prefixWord ++ tailWord_668492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668503 : List Nat := [1, 1, 3, 2, 4, 2, 2, 7]
def baseStart_668503 : Nat := 118140960795 + 668503 * 2 ^ 59
def prefixEnd_668503 : Nat := 4983230072969 + 3 ^ 40 * 668503 * 2
def baseEnd_668503 : Nat := 25426915405385423158379

theorem tailTrace_668503 : CollatzResearch.WordTrace tailWord_668503 prefixEnd_668503 25426915405385423158379 := by
  unfold tailWord_668503
  simp only [CollatzResearch.WordTrace]
  refine ⟨24382307497135277067874163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16254871664756851378582775 24382307497135277067874163)
  ·
    refine ⟨36573461245702915601811245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24382307497135277067874163 36573461245702915601811245)
    ·
      refine ⟨13715047967138593350679217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36573461245702915601811245 13715047967138593350679217)
      ·
        refine ⟨10286285975353945013009413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13715047967138593350679217 10286285975353945013009413)
        ·
          refine ⟨1928678620378864689939265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10286285975353945013009413 1928678620378864689939265)
          ·
            refine ⟨1446508965284148517454449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928678620378864689939265 1446508965284148517454449)
            ·
              refine ⟨1084881723963111388090837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446508965284148517454449 1084881723963111388090837)
              ·
                refine ⟨25426915405385423158379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1084881723963111388090837 25426915405385423158379)
                ·
                  rfl

theorem cell22_668503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 7].length) (baseStart_668503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668503 prefixEnd_668503 := by exact prefixLift 668503
  have htrace : WordTrace (prefixWord ++ tailWord_668503) baseStart_668503 baseEnd_668503 := by
    simpa [prefixWord, tailWord_668503, baseEnd_668503] using wordTrace_append hprefix tailTrace_668503
  have hstable : (prefixWord ++ tailWord_668503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668503).length < 2 ^ (prefixWord ++ tailWord_668503).sum := by decide
  have hdescent : baseEnd_668503 < baseStart_668503 := by decide
  rcases family_descends (prefixWord ++ tailWord_668503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668531 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 9]
def baseStart_668531 : Nat := 118140960795 + 668531 * 2 ^ 59
def prefixEnd_668531 : Nat := 4983230072969 + 3 ^ 40 * 668531 * 2
def baseEnd_668531 : Nat := 76283941206895356241775

theorem tailTrace_668531 : CollatzResearch.WordTrace tailWord_668531 prefixEnd_668531 76283941206895356241775 := by
  unfold tailWord_668531
  simp only [CollatzResearch.WordTrace]
  refine ⟨24383328741033837849893447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16255552494022558566595631 24383328741033837849893447)
  ·
    refine ⟨36574993111550756774840171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24383328741033837849893447 36574993111550756774840171)
    ·
      refine ⟨54862489667326135162260257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36574993111550756774840171 54862489667326135162260257)
      ·
        refine ⟨41146867250494601371695193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54862489667326135162260257 41146867250494601371695193)
        ·
          refine ⟨30860150437870951028771395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41146867250494601371695193 30860150437870951028771395)
          ·
            refine ⟨46290225656806426543157093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30860150437870951028771395 46290225656806426543157093)
            ·
              refine ⟨8679417310651204976841955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46290225656806426543157093 8679417310651204976841955)
              ·
                refine ⟨13019125965976807465262933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8679417310651204976841955 13019125965976807465262933)
                ·
                  refine ⟨76283941206895356241775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13019125965976807465262933 76283941206895356241775)
                  ·
                    rfl

theorem cell22_668531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 9].length) (baseStart_668531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668531 prefixEnd_668531 := by exact prefixLift 668531
  have htrace : WordTrace (prefixWord ++ tailWord_668531) baseStart_668531 baseEnd_668531 := by
    simpa [prefixWord, tailWord_668531, baseEnd_668531] using wordTrace_append hprefix tailTrace_668531
  have hstable : (prefixWord ++ tailWord_668531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668531).length < 2 ^ (prefixWord ++ tailWord_668531).sum := by decide
  have hdescent : baseEnd_668531 < baseStart_668531 := by decide
  rcases family_descends (prefixWord ++ tailWord_668531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668623 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 1, 6]
def baseStart_668623 : Nat := 118140960795 + 668623 * 2 ^ 59
def prefixEnd_668623 : Nat := 4983230072969 + 3 ^ 40 * 668623 * 2
def baseEnd_668623 : Nat := 228883317100828495425043

theorem tailTrace_668623 : CollatzResearch.WordTrace tailWord_668623 prefixEnd_668623 228883317100828495425043 := by
  unfold tailWord_668623
  simp only [CollatzResearch.WordTrace]
  refine ⟨24386684256700537562242523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16257789504467025041495015 24386684256700537562242523)
  ·
    refine ⟨36580026385050806343363785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24386684256700537562242523 36580026385050806343363785)
    ·
      refine ⟨27435019788788104757522839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36580026385050806343363785 27435019788788104757522839)
      ·
        refine ⟨41152529683182157136284259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27435019788788104757522839 41152529683182157136284259)
        ·
          refine ⟨61728794524773235704426389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41152529683182157136284259 61728794524773235704426389)
          ·
            refine ⟨2893537243348745423644987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61728794524773235704426389 2893537243348745423644987)
            ·
              refine ⟨4340305865023118135467481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893537243348745423644987 4340305865023118135467481)
              ·
                refine ⟨3255229398767338601600611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4340305865023118135467481 3255229398767338601600611)
                ·
                  refine ⟨4882844098151007902400917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255229398767338601600611 4882844098151007902400917)
                  ·
                    refine ⟨228883317100828495425043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4882844098151007902400917 228883317100828495425043)
                    ·
                      rfl

theorem cell22_668623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_668623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668623 prefixEnd_668623 := by exact prefixLift 668623
  have htrace : WordTrace (prefixWord ++ tailWord_668623) baseStart_668623 baseEnd_668623 := by
    simpa [prefixWord, tailWord_668623, baseEnd_668623] using wordTrace_append hprefix tailTrace_668623
  have hstable : (prefixWord ++ tailWord_668623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668623).length < 2 ^ (prefixWord ++ tailWord_668623).sum := by decide
  have hdescent : baseEnd_668623 < baseStart_668623 := by decide
  rcases family_descends (prefixWord ++ tailWord_668623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668661 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 6]
def baseStart_668661 : Nat := 118140960795 + 668661 * 2 ^ 59
def prefixEnd_668661 : Nat := 4983230072969 + 3 ^ 40 * 668661 * 2
def baseEnd_668661 : Nat := 76298775092469687658309

theorem tailTrace_668661 : CollatzResearch.WordTrace tailWord_668661 prefixEnd_668661 76298775092469687658309 := by
  unfold tailWord_668661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24388070230562870052125837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16258713487041913368083891 24388070230562870052125837)
  ·
    refine ⟨9145526336461076269547189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24388070230562870052125837 9145526336461076269547189)
    ·
      refine ⟨857393094043225900270049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9145526336461076269547189 857393094043225900270049)
      ·
        refine ⟨643044820532419425202537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 857393094043225900270049 643044820532419425202537)
        ·
          refine ⟨482283615399314568901903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643044820532419425202537 482283615399314568901903)
          ·
            refine ⟨723425423098971853352855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482283615399314568901903 723425423098971853352855)
            ·
              refine ⟨1085138134648457780029283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723425423098971853352855 1085138134648457780029283)
              ·
                refine ⟨1627707201972686670043925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085138134648457780029283 1627707201972686670043925)
                ·
                  refine ⟨76298775092469687658309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1627707201972686670043925 76298775092469687658309)
                  ·
                    rfl

theorem cell22_668661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_668661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668661 prefixEnd_668661 := by exact prefixLift 668661
  have htrace : WordTrace (prefixWord ++ tailWord_668661) baseStart_668661 baseEnd_668661 := by
    simpa [prefixWord, tailWord_668661, baseEnd_668661] using wordTrace_append hprefix tailTrace_668661
  have hstable : (prefixWord ++ tailWord_668661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668661).length < 2 ^ (prefixWord ++ tailWord_668661).sum := by decide
  have hdescent : baseEnd_668661 < baseStart_668661 := by decide
  rcases family_descends (prefixWord ++ tailWord_668661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668730 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_668730 : Nat := 118140960795 + 668730 * 2 ^ 59
def prefixEnd_668730 : Nat := 4983230072969 + 3 ^ 40 * 668730 * 2
def baseEnd_668730 : Nat := 228919945387515882999715

theorem tailTrace_668730 : CollatzResearch.WordTrace tailWord_668730 prefixEnd_668730 228919945387515882999715 := by
  unfold tailWord_668730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6097646716828223709096911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16260391244875263224258429 6097646716828223709096911)
  ·
    refine ⟨9146470075242335563645367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6097646716828223709096911 9146470075242335563645367)
    ·
      refine ⟨13719705112863503345468051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9146470075242335563645367 13719705112863503345468051)
      ·
        refine ⟨20579557669295255018202077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13719705112863503345468051 20579557669295255018202077)
        ·
          refine ⟨7717334125985720631825779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20579557669295255018202077 7717334125985720631825779)
          ·
            refine ⟨11576001188978580947738669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7717334125985720631825779 11576001188978580947738669)
            ·
              refine ⟨4341000445866967855402001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11576001188978580947738669 4341000445866967855402001)
              ·
                refine ⟨3255750334400225891551501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4341000445866967855402001 3255750334400225891551501)
                ·
                  refine ⟨1220906375400084709331813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3255750334400225891551501 1220906375400084709331813)
                  ·
                    refine ⟨228919945387515882999715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1220906375400084709331813 228919945387515882999715)
                    ·
                      rfl

theorem cell22_668730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_668730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668730 prefixEnd_668730 := by exact prefixLift 668730
  have htrace : WordTrace (prefixWord ++ tailWord_668730) baseStart_668730 baseEnd_668730 := by
    simpa [prefixWord, tailWord_668730, baseEnd_668730] using wordTrace_append hprefix tailTrace_668730
  have hstable : (prefixWord ++ tailWord_668730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668730).length < 2 ^ (prefixWord ++ tailWord_668730).sum := by decide
  have hdescent : baseEnd_668730 < baseStart_668730 := by decide
  rcases family_descends (prefixWord ++ tailWord_668730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668760 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_668760 : Nat := 118140960795 + 668760 * 2 ^ 59
def prefixEnd_668760 : Nat := 4983230072969 + 3 ^ 40 * 668760 * 2
def baseEnd_668760 : Nat := 228930215000605804749623

theorem tailTrace_668760 : CollatzResearch.WordTrace tailWord_668760 prefixEnd_668760 228930215000605804749623 := by
  unfold tailWord_668760
  simp only [CollatzResearch.WordTrace]
  refine ⟨12195840528602104979989867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16261120704802806639986489 12195840528602104979989867)
  ·
    refine ⟨18293760792903157469984801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12195840528602104979989867 18293760792903157469984801)
    ·
      refine ⟨13720320594677368102488601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18293760792903157469984801 13720320594677368102488601)
      ·
        refine ⟨10290240446008026076866451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13720320594677368102488601 10290240446008026076866451)
        ·
          refine ⟨15435360669012039115299677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290240446008026076866451 15435360669012039115299677)
          ·
            refine ⟨5788260250879514668237379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15435360669012039115299677 5788260250879514668237379)
            ·
              refine ⟨8682390376319272002356069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788260250879514668237379 8682390376319272002356069)
              ·
                refine ⟨1627948195559863500441763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8682390376319272002356069 1627948195559863500441763)
                ·
                  refine ⟨2441922293339795250662645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1627948195559863500441763 2441922293339795250662645)
                  ·
                    refine ⟨228930215000605804749623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2441922293339795250662645 228930215000605804749623)
                    ·
                      rfl

theorem cell22_668760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_668760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668760 prefixEnd_668760 := by exact prefixLift 668760
  have htrace : WordTrace (prefixWord ++ tailWord_668760) baseStart_668760 baseEnd_668760 := by
    simpa [prefixWord, tailWord_668760, baseEnd_668760] using wordTrace_append hprefix tailTrace_668760
  have hstable : (prefixWord ++ tailWord_668760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668760).length < 2 ^ (prefixWord ++ tailWord_668760).sum := by decide
  have hdescent : baseEnd_668760 < baseStart_668760 := by decide
  rcases family_descends (prefixWord ++ tailWord_668760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668777 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 4, 3]
def baseStart_668777 : Nat := 118140960795 + 668777 * 2 ^ 59
def prefixEnd_668777 : Nat := 4983230072969 + 3 ^ 40 * 668777 * 2
def baseEnd_668777 : Nat := 228936034448023427074571

theorem tailTrace_668777 : CollatzResearch.WordTrace tailWord_668777 prefixEnd_668777 228936034448023427074571 := by
  unfold tailWord_668777
  simp only [CollatzResearch.WordTrace]
  refine ⟨24392301098142621863348585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16261534065428414575565723 24392301098142621863348585)
  ·
    refine ⟨18294225823606966397511439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24392301098142621863348585 18294225823606966397511439)
    ·
      refine ⟨27441338735410449596267159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18294225823606966397511439 27441338735410449596267159)
      ·
        refine ⟨41162008103115674394400739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27441338735410449596267159 41162008103115674394400739)
        ·
          refine ⟨61743012154673511591601109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41162008103115674394400739 61743012154673511591601109)
          ·
            refine ⟨1447101847375160427928151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 61743012154673511591601109 1447101847375160427928151)
            ·
              refine ⟨2170652771062740641892227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447101847375160427928151 2170652771062740641892227)
              ·
                refine ⟨3255979156594110962838341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2170652771062740641892227 3255979156594110962838341)
                ·
                  refine ⟨610496091861395805532189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3255979156594110962838341 610496091861395805532189)
                  ·
                    refine ⟨228936034448023427074571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 610496091861395805532189 228936034448023427074571)
                    ·
                      rfl

theorem cell22_668777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_668777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668777 prefixEnd_668777 := by exact prefixLift 668777
  have htrace : WordTrace (prefixWord ++ tailWord_668777) baseStart_668777 baseEnd_668777 := by
    simpa [prefixWord, tailWord_668777, baseEnd_668777] using wordTrace_append hprefix tailTrace_668777
  have hstable : (prefixWord ++ tailWord_668777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668777).length < 2 ^ (prefixWord ++ tailWord_668777).sum := by decide
  have hdescent : baseEnd_668777 < baseStart_668777 := by decide
  rcases family_descends (prefixWord ++ tailWord_668777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668845 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_668845 : Nat := 118140960795 + 668845 * 2 ^ 59
def prefixEnd_668845 : Nat := 4983230072969 + 3 ^ 40 * 668845 * 2
def baseEnd_668845 : Nat := 228959312237693916374363

theorem tailTrace_668845 : CollatzResearch.WordTrace tailWord_668845 prefixEnd_668845 228959312237693916374363 := by
  unfold tailWord_668845
  simp only [CollatzResearch.WordTrace]
  refine ⟨24394781261896269476823989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16263187507930846317882659 24394781261896269476823989)
  ·
    refine ⟨2287010743302775263452249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24394781261896269476823989 2287010743302775263452249)
    ·
      refine ⟨1715258057477081447589187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2287010743302775263452249 1715258057477081447589187)
      ·
        refine ⟨2572887086215622171383781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715258057477081447589187 2572887086215622171383781)
        ·
          refine ⟨482416328665429157134459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2572887086215622171383781 482416328665429157134459)
          ·
            refine ⟨723624492998143735701689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482416328665429157134459 723624492998143735701689)
            ·
              refine ⟨542718369748607801776267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723624492998143735701689 542718369748607801776267)
              ·
                refine ⟨814077554622911702664401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542718369748607801776267 814077554622911702664401)
                ·
                  refine ⟨610558165967183776998301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814077554622911702664401 610558165967183776998301)
                  ·
                    refine ⟨228959312237693916374363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 610558165967183776998301 228959312237693916374363)
                    ·
                      rfl

theorem cell22_668845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_668845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668845 prefixEnd_668845 := by exact prefixLift 668845
  have htrace : WordTrace (prefixWord ++ tailWord_668845) baseStart_668845 baseEnd_668845 := by
    simpa [prefixWord, tailWord_668845, baseEnd_668845] using wordTrace_append hprefix tailTrace_668845
  have hstable : (prefixWord ++ tailWord_668845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668845).length < 2 ^ (prefixWord ++ tailWord_668845).sum := by decide
  have hdescent : baseEnd_668845 < baseStart_668845 := by decide
  rcases family_descends (prefixWord ++ tailWord_668845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668912 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 8, 3]
def baseStart_668912 : Nat := 118140960795 + 668912 * 2 ^ 59
def prefixEnd_668912 : Nat := 4983230072969 + 3 ^ 40 * 668912 * 2
def baseEnd_668912 : Nat := 228982247706928074949157

theorem tailTrace_668912 : CollatzResearch.WordTrace tailWord_668912 prefixEnd_668912 228982247706928074949157 := by
  unfold tailWord_668912
  simp only [CollatzResearch.WordTrace]
  refine ⟨12198612476326769959756495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16264816635102359946341993 12198612476326769959756495)
  ·
    refine ⟨18297918714490154939634743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12198612476326769959756495 18297918714490154939634743)
    ·
      refine ⟨27446878071735232409452115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18297918714490154939634743 27446878071735232409452115)
      ·
        refine ⟨41170317107602848614178173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27446878071735232409452115 41170317107602848614178173)
        ·
          refine ⟨15438868915351068230316815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41170317107602848614178173 15438868915351068230316815)
          ·
            refine ⟨23158303373026602345475223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15438868915351068230316815 23158303373026602345475223)
            ·
              refine ⟨34737455059539903518212835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23158303373026602345475223 34737455059539903518212835)
              ·
                refine ⟨52106182589309855277319253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34737455059539903518212835 52106182589309855277319253)
                ·
                  refine ⟨610619327218474866531085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 52106182589309855277319253 610619327218474866531085)
                  ·
                    refine ⟨228982247706928074949157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 610619327218474866531085 228982247706928074949157)
                    ·
                      rfl

theorem cell22_668912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_668912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668912 prefixEnd_668912 := by exact prefixLift 668912
  have htrace : WordTrace (prefixWord ++ tailWord_668912) baseStart_668912 baseEnd_668912 := by
    simpa [prefixWord, tailWord_668912, baseEnd_668912] using wordTrace_append hprefix tailTrace_668912
  have hstable : (prefixWord ++ tailWord_668912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668912).length < 2 ^ (prefixWord ++ tailWord_668912).sum := by decide
  have hdescent : baseEnd_668912 < baseStart_668912 := by decide
  rcases family_descends (prefixWord ++ tailWord_668912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668914 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_668914 : Nat := 118140960795 + 668914 * 2 ^ 59
def prefixEnd_668914 : Nat := 4983230072969 + 3 ^ 40 * 668914 * 2
def baseEnd_668914 : Nat := 76327644115933578799717

theorem tailTrace_668914 : CollatzResearch.WordTrace tailWord_668914 prefixEnd_668914 76327644115933578799717 := by
  unfold tailWord_668914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6099324474661573565271449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16264865265764196174057197 6099324474661573565271449)
  ·
    refine ⟨4574493355996180173953587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6099324474661573565271449 4574493355996180173953587)
    ·
      refine ⟨6861740033994270260930381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4574493355996180173953587 6861740033994270260930381)
      ·
        refine ⟨2573152512747851347848893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6861740033994270260930381 2573152512747851347848893)
        ·
          refine ⟨964932192280444255443335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2573152512747851347848893 964932192280444255443335)
          ·
            refine ⟨1447398288420666383165003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964932192280444255443335 1447398288420666383165003)
            ·
              refine ⟨2171097432630999574747505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447398288420666383165003 2171097432630999574747505)
              ·
                refine ⟨1628323074473249681060629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171097432630999574747505 1628323074473249681060629)
                ·
                  refine ⟨76327644115933578799717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1628323074473249681060629 76327644115933578799717)
                  ·
                    rfl

theorem cell22_668914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_668914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668914 prefixEnd_668914 := by exact prefixLift 668914
  have htrace : WordTrace (prefixWord ++ tailWord_668914) baseStart_668914 baseEnd_668914 := by
    simpa [prefixWord, tailWord_668914, baseEnd_668914] using wordTrace_append hprefix tailTrace_668914
  have hstable : (prefixWord ++ tailWord_668914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668914).length < 2 ^ (prefixWord ++ tailWord_668914).sum := by decide
  have hdescent : baseEnd_668914 < baseStart_668914 := by decide
  rcases family_descends (prefixWord ++ tailWord_668914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668927 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 1, 6]
def baseStart_668927 : Nat := 118140960795 + 668927 * 2 ^ 59
def prefixEnd_668927 : Nat := 4983230072969 + 3 ^ 40 * 668927 * 2
def baseEnd_668927 : Nat := 228987382513473035824111

theorem tailTrace_668927 : CollatzResearch.WordTrace tailWord_668927 prefixEnd_668927 228987382513473035824111 := by
  unfold tailWord_668927
  simp only [CollatzResearch.WordTrace]
  refine ⟨24397772047599197481309035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16265181365066131654206023 24397772047599197481309035)
  ·
    refine ⟨36596658071398796221963553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24397772047599197481309035 36596658071398796221963553)
    ·
      refine ⟨27447493553549097166472665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36596658071398796221963553 27447493553549097166472665)
      ·
        refine ⟨20585620165161822874854499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27447493553549097166472665 20585620165161822874854499)
        ·
          refine ⟨30878430247742734312281749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20585620165161822874854499 30878430247742734312281749)
          ·
            refine ⟨1447426417862940670888207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30878430247742734312281749 1447426417862940670888207)
            ·
              refine ⟨2171139626794411006332311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447426417862940670888207 2171139626794411006332311)
              ·
                refine ⟨3256709440191616509498467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171139626794411006332311 3256709440191616509498467)
                ·
                  refine ⟨4885064160287424764247701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3256709440191616509498467 4885064160287424764247701)
                  ·
                    refine ⟨228987382513473035824111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4885064160287424764247701 228987382513473035824111)
                    ·
                      rfl

theorem cell22_668927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_668927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668927 prefixEnd_668927 := by exact prefixLift 668927
  have htrace : WordTrace (prefixWord ++ tailWord_668927) baseStart_668927 baseEnd_668927 := by
    simpa [prefixWord, tailWord_668927, baseEnd_668927] using wordTrace_append hprefix tailTrace_668927
  have hstable : (prefixWord ++ tailWord_668927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668927).length < 2 ^ (prefixWord ++ tailWord_668927).sum := by decide
  have hdescent : baseEnd_668927 < baseStart_668927 := by decide
  rcases family_descends (prefixWord ++ tailWord_668927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668942 : List Nat := [4, 1, 1, 2, 1, 4, 9]
def baseStart_668942 : Nat := 118140960795 + 668942 * 2 ^ 59
def prefixEnd_668942 : Nat := 4983230072969 + 3 ^ 40 * 668942 * 2
def baseEnd_668942 : Nat := 8481204345185851729595

theorem tailTrace_668942 : CollatzResearch.WordTrace tailWord_668942 prefixEnd_668942 8481204345185851729595 := by
  unfold tailWord_668942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3049789892818106880388135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16265546095029903362070053 3049789892818106880388135)
  ·
    refine ⟨4574684839227160320582203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3049789892818106880388135 4574684839227160320582203)
    ·
      refine ⟨6862027258840740480873305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4574684839227160320582203 6862027258840740480873305)
      ·
        refine ⟨5146520444130555360654979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6862027258840740480873305 5146520444130555360654979)
        ·
          refine ⟨7719780666195833040982469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5146520444130555360654979 7719780666195833040982469)
          ·
            refine ⟨1447458874911718695184213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7719780666195833040982469 1447458874911718695184213)
            ·
              refine ⟨8481204345185851729595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1447458874911718695184213 8481204345185851729595)
              ·
                rfl

theorem cell22_668942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 9].length) (baseStart_668942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668942 prefixEnd_668942 := by exact prefixLift 668942
  have htrace : WordTrace (prefixWord ++ tailWord_668942) baseStart_668942 baseEnd_668942 := by
    simpa [prefixWord, tailWord_668942, baseEnd_668942] using wordTrace_append hprefix tailTrace_668942
  have hstable : (prefixWord ++ tailWord_668942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668942).length < 2 ^ (prefixWord ++ tailWord_668942).sum := by decide
  have hdescent : baseEnd_668942 < baseStart_668942 := by decide
  rcases family_descends (prefixWord ++ tailWord_668942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668982 : List Nat := [5, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_668982 : Nat := 118140960795 + 668982 * 2 ^ 59
def prefixEnd_668982 : Nat := 4983230072969 + 3 ^ 40 * 668982 * 2
def baseEnd_668982 : Nat := 76335403379157075232981

theorem tailTrace_668982 : CollatzResearch.WordTrace tailWord_668982 prefixEnd_668982 76335403379157075232981 := by
  unfold tailWord_668982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524986128899996367160075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16266518708266627916374133 1524986128899996367160075)
  ·
    refine ⟨2287479193349994550740113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1524986128899996367160075 2287479193349994550740113)
    ·
      refine ⟨1715609395012495913055085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2287479193349994550740113 1715609395012495913055085)
      ·
        refine ⟨643353523129685967395657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1715609395012495913055085 643353523129685967395657)
        ·
          refine ⟨482515142347264475546743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643353523129685967395657 482515142347264475546743)
          ·
            refine ⟨723772713520896713320115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482515142347264475546743 723772713520896713320115)
            ·
              refine ⟨1085659070281345069980173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723772713520896713320115 1085659070281345069980173)
              ·
                refine ⟨407122151355504401242565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085659070281345069980173 407122151355504401242565)
                ·
                  refine ⟨76335403379157075232981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407122151355504401242565 76335403379157075232981)
                  ·
                    rfl

theorem cell22_668982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_668982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_668982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_668982 prefixEnd_668982 := by exact prefixLift 668982
  have htrace : WordTrace (prefixWord ++ tailWord_668982) baseStart_668982 baseEnd_668982 := by
    simpa [prefixWord, tailWord_668982, baseEnd_668982] using wordTrace_append hprefix tailTrace_668982
  have hstable : (prefixWord ++ tailWord_668982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668982).length < 2 ^ (prefixWord ++ tailWord_668982).sum := by decide
  have hdescent : baseEnd_668982 < baseStart_668982 := by decide
  rcases family_descends (prefixWord ++ tailWord_668982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669002 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_669002 : Nat := 118140960795 + 669002 * 2 ^ 59
def prefixEnd_669002 : Nat := 4983230072969 + 3 ^ 40 * 669002 * 2
def baseEnd_669002 : Nat := 229013056546197840198881

theorem tailTrace_669002 : CollatzResearch.WordTrace tailWord_669002 prefixEnd_669002 229013056546197840198881 := by
  unfold tailWord_669002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6100126880581871322572315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16267005014884990193526173 6100126880581871322572315)
  ·
    refine ⟨9150190320872806983858473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6100126880581871322572315 9150190320872806983858473)
    ·
      refine ⟨6862642740654605237893855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9150190320872806983858473 6862642740654605237893855)
      ·
        refine ⟨10293964110981907856840783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6862642740654605237893855 10293964110981907856840783)
        ·
          refine ⟨15440946166472861785261175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10293964110981907856840783 15440946166472861785261175)
          ·
            refine ⟨23161419249709292677891763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15440946166472861785261175 23161419249709292677891763)
            ·
              refine ⟨34742128874563939016837645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23161419249709292677891763 34742128874563939016837645)
              ·
                refine ⟨13028298327961477131314117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34742128874563939016837645 13028298327961477131314117)
                ·
                  refine ⟨2442805936492776962121397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13028298327961477131314117 2442805936492776962121397)
                  ·
                    refine ⟨229013056546197840198881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2442805936492776962121397 229013056546197840198881)
                    ·
                      rfl

theorem cell22_669002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_669002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669002 prefixEnd_669002 := by exact prefixLift 669002
  have htrace : WordTrace (prefixWord ++ tailWord_669002) baseStart_669002 baseEnd_669002 := by
    simpa [prefixWord, tailWord_669002, baseEnd_669002] using wordTrace_append hprefix tailTrace_669002
  have hstable : (prefixWord ++ tailWord_669002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669002).length < 2 ^ (prefixWord ++ tailWord_669002).sum := by decide
  have hdescent : baseEnd_669002 < baseStart_669002 := by decide
  rcases family_descends (prefixWord ++ tailWord_669002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669008 : List Nat := [2, 1, 1, 1, 1, 5, 5, 2, 1, 3]
def baseStart_669008 : Nat := 118140960795 + 669008 * 2 ^ 59
def prefixEnd_669008 : Nat := 4983230072969 + 3 ^ 40 * 669008 * 2
def baseEnd_669008 : Nat := 229015110468815824548863

theorem tailTrace_669008 : CollatzResearch.WordTrace tailWord_669008 prefixEnd_669008 229015110468815824548863 := by
  unfold tailWord_669008
  simp only [CollatzResearch.WordTrace]
  refine ⟨12200363180152874157503839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16267150906870498876671785 12200363180152874157503839)
  ·
    refine ⟨18300544770229311236255759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12200363180152874157503839 18300544770229311236255759)
    ·
      refine ⟨27450817155343966854383639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18300544770229311236255759 27450817155343966854383639)
      ·
        refine ⟨41176225733015950281575459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27450817155343966854383639 41176225733015950281575459)
        ·
          refine ⟨61764338599523925422363189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41176225733015950281575459 61764338599523925422363189)
          ·
            refine ⟨5790406743705368008346549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61764338599523925422363189 5790406743705368008346549)
            ·
              refine ⟨542850632222378250782489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5790406743705368008346549 542850632222378250782489)
              ·
                refine ⟨407137974166783688086867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542850632222378250782489 407137974166783688086867)
                ·
                  refine ⟨610706961250175532130301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407137974166783688086867 610706961250175532130301)
                  ·
                    refine ⟨229015110468815824548863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 610706961250175532130301 229015110468815824548863)
                    ·
                      rfl

theorem cell22_669008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 3].length) (baseStart_669008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669008 prefixEnd_669008 := by exact prefixLift 669008
  have htrace : WordTrace (prefixWord ++ tailWord_669008) baseStart_669008 baseEnd_669008 := by
    simpa [prefixWord, tailWord_669008, baseEnd_669008] using wordTrace_append hprefix tailTrace_669008
  have hstable : (prefixWord ++ tailWord_669008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669008).length < 2 ^ (prefixWord ++ tailWord_669008).sum := by decide
  have hdescent : baseEnd_669008 < baseStart_669008 := by decide
  rcases family_descends (prefixWord ++ tailWord_669008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669051 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 1, 4]
def baseStart_669051 : Nat := 118140960795 + 669051 * 2 ^ 59
def prefixEnd_669051 : Nat := 4983230072969 + 3 ^ 40 * 669051 * 2
def baseEnd_669051 : Nat := 229029830247578045723731

theorem tailTrace_669051 : CollatzResearch.WordTrace tailWord_669051 prefixEnd_669051 229029830247578045723731 := by
  unfold tailWord_669051
  simp only [CollatzResearch.WordTrace]
  refine ⟨24402294699149966658823007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16268196466099977772548671 24402294699149966658823007)
  ·
    refine ⟨36603442048724949988234511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24402294699149966658823007 36603442048724949988234511)
    ·
      refine ⟨54905163073087424982351767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36603442048724949988234511 54905163073087424982351767)
      ·
        refine ⟨82357744609631137473527651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54905163073087424982351767 82357744609631137473527651)
        ·
          refine ⟨123536616914446706210291477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82357744609631137473527651 123536616914446706210291477)
          ·
            refine ⟨5790778917864689353607413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123536616914446706210291477 5790778917864689353607413)
            ·
              refine ⟨542885523549814626900695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5790778917864689353607413 542885523549814626900695)
              ·
                refine ⟨814328285324721940351043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542885523549814626900695 814328285324721940351043)
                ·
                  refine ⟨1221492427987082910526565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814328285324721940351043 1221492427987082910526565)
                  ·
                    refine ⟨229029830247578045723731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221492427987082910526565 229029830247578045723731)
                    ·
                      rfl

theorem cell22_669051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 4].length) (baseStart_669051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669051 prefixEnd_669051 := by exact prefixLift 669051
  have htrace : WordTrace (prefixWord ++ tailWord_669051) baseStart_669051 baseEnd_669051 := by
    simpa [prefixWord, tailWord_669051, baseEnd_669051] using wordTrace_append hprefix tailTrace_669051
  have hstable : (prefixWord ++ tailWord_669051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669051).length < 2 ^ (prefixWord ++ tailWord_669051).sum := by decide
  have hdescent : baseEnd_669051 < baseStart_669051 := by decide
  rcases family_descends (prefixWord ++ tailWord_669051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669081 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 2, 3]
def baseStart_669081 : Nat := 118140960795 + 669081 * 2 ^ 59
def prefixEnd_669081 : Nat := 4983230072969 + 3 ^ 40 * 669081 * 2
def baseEnd_669081 : Nat := 229040099860667967473639

theorem tailTrace_669081 : CollatzResearch.WordTrace tailWord_669081 prefixEnd_669081 229040099860667967473639 := by
  unfold tailWord_669081
  simp only [CollatzResearch.WordTrace]
  refine ⟨24403388889041281782415097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16268925926027521188276731 24403388889041281782415097)
  ·
    refine ⟨18302541666780961336811323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24403388889041281782415097 18302541666780961336811323)
    ·
      refine ⟨27453812500171442005216985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18302541666780961336811323 27453812500171442005216985)
      ·
        refine ⟨20590359375128581503912739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27453812500171442005216985 20590359375128581503912739)
        ·
          refine ⟨30885539062692872255869109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20590359375128581503912739 30885539062692872255869109)
          ·
            refine ⟨2895519287127456773987729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30885539062692872255869109 2895519287127456773987729)
            ·
              refine ⟨2171639465345592580490797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2895519287127456773987729 2171639465345592580490797)
              ·
                refine ⟨814364799504597217684049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2171639465345592580490797 814364799504597217684049)
                ·
                  refine ⟨610773599628447913263037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814364799504597217684049 610773599628447913263037)
                  ·
                    refine ⟨229040099860667967473639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 610773599628447913263037 229040099860667967473639)
                    ·
                      rfl

theorem cell22_669081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_669081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669081 prefixEnd_669081 := by exact prefixLift 669081
  have htrace : WordTrace (prefixWord ++ tailWord_669081) baseStart_669081 baseEnd_669081 := by
    simpa [prefixWord, tailWord_669081, baseEnd_669081] using wordTrace_append hprefix tailTrace_669081
  have hstable : (prefixWord ++ tailWord_669081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669081).length < 2 ^ (prefixWord ++ tailWord_669081).sum := by decide
  have hdescent : baseEnd_669081 < baseStart_669081 := by decide
  rcases family_descends (prefixWord ++ tailWord_669081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669203 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 1, 4]
def baseStart_669203 : Nat := 118140960795 + 669203 * 2 ^ 59
def prefixEnd_669203 : Nat := 4983230072969 + 3 ^ 40 * 669203 * 2
def baseEnd_669203 : Nat := 229081862953900315923265

theorem tailTrace_669203 : CollatzResearch.WordTrace tailWord_669203 prefixEnd_669203 229081862953900315923265 := by
  unfold tailWord_669203
  simp only [CollatzResearch.WordTrace]
  refine ⟨24407838594599296618356263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16271892396399531078904175 24407838594599296618356263)
  ·
    refine ⟨36611757891898944927534395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24407838594599296618356263 36611757891898944927534395)
    ·
      refine ⟨54917636837848417391301593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36611757891898944927534395 54917636837848417391301593)
      ·
        refine ⟨41188227628386313043476195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54917636837848417391301593 41188227628386313043476195)
        ·
          refine ⟨61782341442579469565214293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41188227628386313043476195 61782341442579469565214293)
          ·
            refine ⟨724011813780228158967355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 61782341442579469565214293 724011813780228158967355)
            ·
              refine ⟨1086017720670342238451033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724011813780228158967355 1086017720670342238451033)
              ·
                refine ⟨814513290502756678838275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086017720670342238451033 814513290502756678838275)
                ·
                  refine ⟨1221769935754135018257413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814513290502756678838275 1221769935754135018257413)
                  ·
                    refine ⟨229081862953900315923265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221769935754135018257413 229081862953900315923265)
                    ·
                      rfl

theorem cell22_669203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 4].length) (baseStart_669203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669203 prefixEnd_669203 := by exact prefixLift 669203
  have htrace : WordTrace (prefixWord ++ tailWord_669203) baseStart_669203 baseEnd_669203 := by
    simpa [prefixWord, tailWord_669203, baseEnd_669203] using wordTrace_append hprefix tailTrace_669203
  have hstable : (prefixWord ++ tailWord_669203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669203).length < 2 ^ (prefixWord ++ tailWord_669203).sum := by decide
  have hdescent : baseEnd_669203 < baseStart_669203 := by decide
  rcases family_descends (prefixWord ++ tailWord_669203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669216 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_669216 : Nat := 118140960795 + 669216 * 2 ^ 59
def prefixEnd_669216 : Nat := 4983230072969 + 3 ^ 40 * 669216 * 2
def baseEnd_669216 : Nat := 229086313119572615348225

theorem tailTrace_669216 : CollatzResearch.WordTrace tailWord_669216 prefixEnd_669216 229086313119572615348225 := by
  unfold tailWord_669216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12204156371776099919289751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16272208495701466559053001 12204156371776099919289751)
  ·
    refine ⟨18306234557664149878934627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12204156371776099919289751 18306234557664149878934627)
    ·
      refine ⟨27459351836496224818401941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18306234557664149878934627 27459351836496224818401941)
      ·
        refine ⟨1287157117335760538362591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27459351836496224818401941 1287157117335760538362591)
        ·
          refine ⟨1930735676003640807543887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287157117335760538362591 1930735676003640807543887)
          ·
            refine ⟨2896103514005461211315831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930735676003640807543887 2896103514005461211315831)
            ·
              refine ⟨4344155271008191816973747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896103514005461211315831 4344155271008191816973747)
              ·
                refine ⟨6516232906512287725460621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4344155271008191816973747 6516232906512287725460621)
                ·
                  refine ⟨2443587339942107897047733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6516232906512287725460621 2443587339942107897047733)
                  ·
                    refine ⟨229086313119572615348225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2443587339942107897047733 229086313119572615348225)
                    ·
                      rfl

theorem cell22_669216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_669216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669216 prefixEnd_669216 := by exact prefixLift 669216
  have htrace : WordTrace (prefixWord ++ tailWord_669216) baseStart_669216 baseEnd_669216 := by
    simpa [prefixWord, tailWord_669216, baseEnd_669216] using wordTrace_append hprefix tailTrace_669216
  have hstable : (prefixWord ++ tailWord_669216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669216).length < 2 ^ (prefixWord ++ tailWord_669216).sum := by decide
  have hdescent : baseEnd_669216 < baseStart_669216 := by decide
  rcases family_descends (prefixWord ++ tailWord_669216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669235 : List Nat := [1, 1, 1, 2, 4, 5, 2, 2, 4]
def baseStart_669235 : Nat := 118140960795 + 669235 * 2 ^ 59
def prefixEnd_669235 : Nat := 4983230072969 + 3 ^ 40 * 669235 * 2
def baseEnd_669235 : Nat := 76364272402620966374389

theorem tailTrace_669235 : CollatzResearch.WordTrace tailWord_669235 prefixEnd_669235 76364272402620966374389 := by
  unfold tailWord_669235
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409005730483366083521159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16272670486988910722347439 24409005730483366083521159)
  ·
    refine ⟨36613508595725049125281739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24409005730483366083521159 36613508595725049125281739)
    ·
      refine ⟨54920262893587573687922609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36613508595725049125281739 54920262893587573687922609)
      ·
        refine ⟨41190197170190680265941957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54920262893587573687922609 41190197170190680265941957)
        ·
          refine ⟨7723161969410752549864117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41190197170190680265941957 7723161969410752549864117)
          ·
            refine ⟨724046434632258051549761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7723161969410752549864117 724046434632258051549761)
            ·
              refine ⟨543034825974193538662321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724046434632258051549761 543034825974193538662321)
              ·
                refine ⟨407276119480645153996741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543034825974193538662321 407276119480645153996741)
                ·
                  refine ⟨76364272402620966374389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407276119480645153996741 76364272402620966374389)
                  ·
                    rfl

theorem cell22_669235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 4].length) (baseStart_669235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669235 prefixEnd_669235 := by exact prefixLift 669235
  have htrace : WordTrace (prefixWord ++ tailWord_669235) baseStart_669235 baseEnd_669235 := by
    simpa [prefixWord, tailWord_669235, baseEnd_669235] using wordTrace_append hprefix tailTrace_669235
  have hstable : (prefixWord ++ tailWord_669235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669235).length < 2 ^ (prefixWord ++ tailWord_669235).sum := by decide
  have hdescent : baseEnd_669235 < baseStart_669235 := by decide
  rcases family_descends (prefixWord ++ tailWord_669235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669259 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 4, 6]
def baseStart_669259 : Nat := 118140960795 + 669259 * 2 ^ 59
def prefixEnd_669259 : Nat := 4983230072969 + 3 ^ 40 * 669259 * 2
def baseEnd_669259 : Nat := 229101032898334836523093

theorem tailTrace_669259 : CollatzResearch.WordTrace tailWord_669259 prefixEnd_669259 229101032898334836523093 := by
  unfold tailWord_669259
  simp only [CollatzResearch.WordTrace]
  refine ⟨24409881082396418182394831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16273254054930945454929887 24409881082396418182394831)
  ·
    refine ⟨36614821623594627273592247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24409881082396418182394831 36614821623594627273592247)
    ·
      refine ⟨54922232435391940910388371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36614821623594627273592247 54922232435391940910388371)
      ·
        refine ⟨82383348653087911365582557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54922232435391940910388371 82383348653087911365582557)
        ·
          refine ⟨30893755744907966762093459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82383348653087911365582557 30893755744907966762093459)
          ·
            refine ⟨46340633617361950143140189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30893755744907966762093459 46340633617361950143140189)
            ·
              refine ⟨17377737606510731303677571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46340633617361950143140189 17377737606510731303677571)
              ·
                refine ⟨26066606409766096955516357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17377737606510731303677571 26066606409766096955516357)
                ·
                  refine ⟨4887488701831143179159317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26066606409766096955516357 4887488701831143179159317)
                  ·
                    refine ⟨229101032898334836523093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4887488701831143179159317 229101032898334836523093)
                    ·
                      rfl

theorem cell22_669259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_669259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669259 prefixEnd_669259 := by exact prefixLift 669259
  have htrace : WordTrace (prefixWord ++ tailWord_669259) baseStart_669259 baseEnd_669259 := by
    simpa [prefixWord, tailWord_669259, baseEnd_669259] using wordTrace_append hprefix tailTrace_669259
  have hstable : (prefixWord ++ tailWord_669259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669259).length < 2 ^ (prefixWord ++ tailWord_669259).sum := by decide
  have hdescent : baseEnd_669259 < baseStart_669259 := by decide
  rcases family_descends (prefixWord ++ tailWord_669259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669321 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_669321 : Nat := 118140960795 + 669321 * 2 ^ 59
def prefixEnd_669321 : Nat := 4983230072969 + 3 ^ 40 * 669321 * 2
def baseEnd_669321 : Nat := 229122256765387341472903

theorem tailTrace_669321 : CollatzResearch.WordTrace tailWord_669321 prefixEnd_669321 229122256765387341472903 := by
  unfold tailWord_669321
  simp only [CollatzResearch.WordTrace]
  refine ⟨24412142408171802771151817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16274761605447868514101211 24412142408171802771151817)
  ·
    refine ⟨18309106806128852078363863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24412142408171802771151817 18309106806128852078363863)
    ·
      refine ⟨27463660209193278117545795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18309106806128852078363863 27463660209193278117545795)
      ·
        refine ⟨41195490313789917176318693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27463660209193278117545795 41195490313789917176318693)
        ·
          refine ⟨7724154433835609470559755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41195490313789917176318693 7724154433835609470559755)
          ·
            refine ⟨11586231650753414205839633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724154433835609470559755 11586231650753414205839633)
            ·
              refine ⟨8689673738065060654379725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11586231650753414205839633 8689673738065060654379725)
              ·
                refine ⟨3258627651774397745392397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8689673738065060654379725 3258627651774397745392397)
                ·
                  refine ⟨1221985369415399154522149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3258627651774397745392397 1221985369415399154522149)
                  ·
                    refine ⟨229122256765387341472903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1221985369415399154522149 229122256765387341472903)
                    ·
                      rfl

theorem cell22_669321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_669321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669321 prefixEnd_669321 := by exact prefixLift 669321
  have htrace : WordTrace (prefixWord ++ tailWord_669321) baseStart_669321 baseEnd_669321 := by
    simpa [prefixWord, tailWord_669321, baseEnd_669321] using wordTrace_append hprefix tailTrace_669321
  have hstable : (prefixWord ++ tailWord_669321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669321).length < 2 ^ (prefixWord ++ tailWord_669321).sum := by decide
  have hdescent : baseEnd_669321 < baseStart_669321 := by decide
  rcases family_descends (prefixWord ++ tailWord_669321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669346 : List Nat := [3, 3, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_669346 : Nat := 118140960795 + 669346 * 2 ^ 59
def prefixEnd_669346 : Nat := 4983230072969 + 3 ^ 40 * 669346 * 2
def baseEnd_669346 : Nat := 229130814776295609597827

theorem tailTrace_669346 : CollatzResearch.WordTrace tailWord_669346 prefixEnd_669346 229130814776295609597827 := by
  unfold tailWord_669346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103263558270308010202973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16275369488720821360541261 6103263558270308010202973)
  ·
    refine ⟨2288723834351365503826115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6103263558270308010202973 2288723834351365503826115)
    ·
      refine ⟨3433085751527048255739173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288723834351365503826115 3433085751527048255739173)
      ·
        refine ⟨643703578411321547951095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3433085751527048255739173 643703578411321547951095)
        ·
          refine ⟨965555367616982321926643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643703578411321547951095 965555367616982321926643)
          ·
            refine ⟨1448333051425473482889965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965555367616982321926643 1448333051425473482889965)
            ·
              refine ⟨543124894284552556083737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1448333051425473482889965 543124894284552556083737)
              ·
                refine ⟨407343670713414417062803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543124894284552556083737 407343670713414417062803)
                ·
                  refine ⟨611015506070121625594205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407343670713414417062803 611015506070121625594205)
                  ·
                    refine ⟨229130814776295609597827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 611015506070121625594205 229130814776295609597827)
                    ·
                      rfl

theorem cell22_669346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_669346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669346 prefixEnd_669346 := by exact prefixLift 669346
  have htrace : WordTrace (prefixWord ++ tailWord_669346) baseStart_669346 baseEnd_669346 := by
    simpa [prefixWord, tailWord_669346, baseEnd_669346] using wordTrace_append hprefix tailTrace_669346
  have hstable : (prefixWord ++ tailWord_669346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669346).length < 2 ^ (prefixWord ++ tailWord_669346).sum := by decide
  have hdescent : baseEnd_669346 < baseStart_669346 := by decide
  rcases family_descends (prefixWord ++ tailWord_669346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669383 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 2, 4]
def baseStart_669383 : Nat := 118140960795 + 669383 * 2 ^ 59
def prefixEnd_669383 : Nat := 4983230072969 + 3 ^ 40 * 669383 * 2
def baseEnd_669383 : Nat := 229143480632439846422713

theorem tailTrace_669383 : CollatzResearch.WordTrace tailWord_669383 prefixEnd_669383 229143480632439846422713 := by
  unfold tailWord_669383
  simp only [CollatzResearch.WordTrace]
  refine ⟨24414403733947187359908803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16276269155964791573272535 24414403733947187359908803)
  ·
    refine ⟨36621605600920781039863205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24414403733947187359908803 36621605600920781039863205)
    ·
      refine ⟨6866551050172646444974351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36621605600920781039863205 6866551050172646444974351)
      ·
        refine ⟨10299826575258969667461527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6866551050172646444974351 10299826575258969667461527)
        ·
          refine ⟨15449739862888454501192291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10299826575258969667461527 15449739862888454501192291)
          ·
            refine ⟨23174609794332681751788437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15449739862888454501192291 23174609794332681751788437)
            ·
              refine ⟨1086309834109344457115083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23174609794332681751788437 1086309834109344457115083)
              ·
                refine ⟨1629464751164016685672625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086309834109344457115083 1629464751164016685672625)
                ·
                  refine ⟨1222098563373012514254469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1629464751164016685672625 1222098563373012514254469)
                  ·
                    refine ⟨229143480632439846422713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1222098563373012514254469 229143480632439846422713)
                    ·
                      rfl

theorem cell22_669383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_669383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669383 prefixEnd_669383 := by exact prefixLift 669383
  have htrace : WordTrace (prefixWord ++ tailWord_669383) baseStart_669383 baseEnd_669383 := by
    simpa [prefixWord, tailWord_669383, baseEnd_669383] using wordTrace_append hprefix tailTrace_669383
  have hstable : (prefixWord ++ tailWord_669383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669383).length < 2 ^ (prefixWord ++ tailWord_669383).sum := by decide
  have hdescent : baseEnd_669383 < baseStart_669383 := by decide
  rcases family_descends (prefixWord ++ tailWord_669383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669389 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_669389 : Nat := 118140960795 + 669389 * 2 ^ 59
def prefixEnd_669389 : Nat := 4983230072969 + 3 ^ 40 * 669389 * 2
def baseEnd_669389 : Nat := 229145534555057830772695

theorem tailTrace_669389 : CollatzResearch.WordTrace tailWord_669389 prefixEnd_669389 229145534555057830772695 := by
  unfold tailWord_669389
  simp only [CollatzResearch.WordTrace]
  refine ⟨24414622571925450384627221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16276415047950300256418147 24414622571925450384627221)
  ·
    refine ⟨1144435433059005486779401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24414622571925450384627221 1144435433059005486779401)
    ·
      refine ⟨858326574794254115084551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1144435433059005486779401 858326574794254115084551)
      ·
        refine ⟨1287489862191381172626827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858326574794254115084551 1287489862191381172626827)
        ·
          refine ⟨1931234793287071758940241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287489862191381172626827 1931234793287071758940241)
          ·
            refine ⟨1448426094965303819205181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1931234793287071758940241 1448426094965303819205181)
            ·
              refine ⟨543159785611988932201943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1448426094965303819205181 543159785611988932201943)
              ·
                refine ⟨814739678417983398302915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543159785611988932201943 814739678417983398302915)
                ·
                  refine ⟨1222109517626975097454373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814739678417983398302915 1222109517626975097454373)
                  ·
                    refine ⟨229145534555057830772695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1222109517626975097454373 229145534555057830772695)
                    ·
                      rfl

theorem cell22_669389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_669389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669389 prefixEnd_669389 := by exact prefixLift 669389
  have htrace : WordTrace (prefixWord ++ tailWord_669389) baseStart_669389 baseEnd_669389 := by
    simpa [prefixWord, tailWord_669389, baseEnd_669389] using wordTrace_append hprefix tailTrace_669389
  have hstable : (prefixWord ++ tailWord_669389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669389).length < 2 ^ (prefixWord ++ tailWord_669389).sum := by decide
  have hdescent : baseEnd_669389 < baseStart_669389 := by decide
  rcases family_descends (prefixWord ++ tailWord_669389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669430 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_669430 : Nat := 118140960795 + 669430 * 2 ^ 59
def prefixEnd_669430 : Nat := 4983230072969 + 3 ^ 40 * 669430 * 2
def baseEnd_669430 : Nat := 229159569692947390497569

theorem tailTrace_669430 : CollatzResearch.WordTrace tailWord_669430 prefixEnd_669430 229159569692947390497569 := by
  unfold tailWord_669430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526007372798557149179359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16277411976517942924579829 1526007372798557149179359)
  ·
    refine ⟨2289011059197835723769039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1526007372798557149179359 2289011059197835723769039)
    ·
      refine ⟨3433516588796753585653559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2289011059197835723769039 3433516588796753585653559)
      ·
        refine ⟨5150274883195130378480339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433516588796753585653559 5150274883195130378480339)
        ·
          refine ⟨7725412324792695567720509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5150274883195130378480339 7725412324792695567720509)
          ·
            refine ⟨2897029621797260837895191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7725412324792695567720509 2897029621797260837895191)
            ·
              refine ⟨4345544432695891256842787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897029621797260837895191 4345544432695891256842787)
              ·
                refine ⟨6518316649043836885264181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4345544432695891256842787 6518316649043836885264181)
                ·
                  refine ⟨611092185847859707993517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6518316649043836885264181 611092185847859707993517)
                  ·
                    refine ⟨229159569692947390497569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 611092185847859707993517 229159569692947390497569)
                    ·
                      rfl

theorem cell22_669430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_669430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669430 prefixEnd_669430 := by exact prefixLift 669430
  have htrace : WordTrace (prefixWord ++ tailWord_669430) baseStart_669430 baseEnd_669430 := by
    simpa [prefixWord, tailWord_669430, baseEnd_669430] using wordTrace_append hprefix tailTrace_669430
  have hstable : (prefixWord ++ tailWord_669430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669430).length < 2 ^ (prefixWord ++ tailWord_669430).sum := by decide
  have hdescent : baseEnd_669430 < baseStart_669430 := by decide
  rcases family_descends (prefixWord ++ tailWord_669430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669490 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_669490 : Nat := 118140960795 + 669490 * 2 ^ 59
def prefixEnd_669490 : Nat := 4983230072969 + 3 ^ 40 * 669490 * 2
def baseEnd_669490 : Nat := 229180108919127233997385

theorem tailTrace_669490 : CollatzResearch.WordTrace tailWord_669490 prefixEnd_669490 229180108919127233997385 := by
  unfold tailWord_669490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6104576586139886158513481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16278870896373029756035949 6104576586139886158513481)
  ·
    refine ⟨4578432439604914618885111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6104576586139886158513481 4578432439604914618885111)
    ·
      refine ⟨6867648659407371928327667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4578432439604914618885111 6867648659407371928327667)
      ·
        refine ⟨10301472989111057892491501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6867648659407371928327667 10301472989111057892491501)
        ·
          refine ⟨3863052370916646709684313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10301472989111057892491501 3863052370916646709684313)
          ·
            refine ⟨2897289278187485032263235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3863052370916646709684313 2897289278187485032263235)
            ·
              refine ⟨4345933917281227548394853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897289278187485032263235 4345933917281227548394853)
              ·
                refine ⟨814862609490230165324035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4345933917281227548394853 814862609490230165324035)
                ·
                  refine ⟨1222293914235345247986053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 814862609490230165324035 1222293914235345247986053)
                  ·
                    refine ⟨229180108919127233997385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1222293914235345247986053 229180108919127233997385)
                    ·
                      rfl

theorem cell22_669490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_669490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669490 prefixEnd_669490 := by exact prefixLift 669490
  have htrace : WordTrace (prefixWord ++ tailWord_669490) baseStart_669490 baseEnd_669490 := by
    simpa [prefixWord, tailWord_669490, baseEnd_669490] using wordTrace_append hprefix tailTrace_669490
  have hstable : (prefixWord ++ tailWord_669490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669490).length < 2 ^ (prefixWord ++ tailWord_669490).sum := by decide
  have hdescent : baseEnd_669490 < baseStart_669490 := by decide
  rcases family_descends (prefixWord ++ tailWord_669490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669520 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 2, 3]
def baseStart_669520 : Nat := 118140960795 + 669520 * 2 ^ 59
def prefixEnd_669520 : Nat := 4983230072969 + 3 ^ 40 * 669520 * 2
def baseEnd_669520 : Nat := 229190378532217155747293

theorem tailTrace_669520 : CollatzResearch.WordTrace tailWord_669520 prefixEnd_669520 229190378532217155747293 := by
  unfold tailWord_669520
  simp only [CollatzResearch.WordTrace]
  refine ⟨12209700267225429878823007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16279600356300573171764009 12209700267225429878823007)
  ·
    refine ⟨18314550400838144818234511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12209700267225429878823007 18314550400838144818234511)
    ·
      refine ⟨27471825601257217227351767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18314550400838144818234511 27471825601257217227351767)
      ·
        refine ⟨41207738401885825841027651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27471825601257217227351767 41207738401885825841027651)
        ·
          refine ⟨61811607602828738761541477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41207738401885825841027651 61811607602828738761541477)
          ·
            refine ⟨11589676425530388517789027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61811607602828738761541477 11589676425530388517789027)
            ·
              refine ⟨17384514638295582776683541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11589676425530388517789027 17384514638295582776683541)
              ·
                refine ⟨814899123670105442657041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17384514638295582776683541 814899123670105442657041)
                ·
                  refine ⟨611174342752579081992781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814899123670105442657041 611174342752579081992781)
                  ·
                    refine ⟨229190378532217155747293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 611174342752579081992781 229190378532217155747293)
                    ·
                      rfl

theorem cell22_669520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_669520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669520 prefixEnd_669520 := by exact prefixLift 669520
  have htrace : WordTrace (prefixWord ++ tailWord_669520) baseStart_669520 baseEnd_669520 := by
    simpa [prefixWord, tailWord_669520, baseEnd_669520] using wordTrace_append hprefix tailTrace_669520
  have hstable : (prefixWord ++ tailWord_669520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669520).length < 2 ^ (prefixWord ++ tailWord_669520).sum := by decide
  have hdescent : baseEnd_669520 < baseStart_669520 := by decide
  rcases family_descends (prefixWord ++ tailWord_669520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669550 : List Nat := [4, 1, 2, 3, 1, 1, 2, 8]
def baseStart_669550 : Nat := 118140960795 + 669550 * 2 ^ 59
def prefixEnd_669550 : Nat := 4983230072969 + 3 ^ 40 * 669550 * 2
def baseEnd_669550 : Nat := 25466738682811897499689

theorem tailTrace_669550 : CollatzResearch.WordTrace tailWord_669550 prefixEnd_669550 25466738682811897499689 := by
  unfold tailWord_669550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052561840542771860154763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16280329816228116587492069 3052561840542771860154763)
  ·
    refine ⟨4578842760814157790232145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3052561840542771860154763 4578842760814157790232145)
    ·
      refine ⟨3434132070610618342674109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4578842760814157790232145 3434132070610618342674109)
      ·
        refine ⟨1287799526478981878502791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3434132070610618342674109 1287799526478981878502791)
        ·
          refine ⟨1931699289718472817754187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287799526478981878502791 1931699289718472817754187)
          ·
            refine ⟨2897548934577709226631281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931699289718472817754187 2897548934577709226631281)
            ·
              refine ⟨2173161700933281919973461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897548934577709226631281 2173161700933281919973461)
              ·
                refine ⟨25466738682811897499689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2173161700933281919973461 25466738682811897499689)
                ·
                  rfl

theorem cell22_669550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_669550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669550 prefixEnd_669550 := by exact prefixLift 669550
  have htrace : WordTrace (prefixWord ++ tailWord_669550) baseStart_669550 baseEnd_669550 := by
    simpa [prefixWord, tailWord_669550, baseEnd_669550] using wordTrace_append hprefix tailTrace_669550
  have hstable : (prefixWord ++ tailWord_669550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669550).length < 2 ^ (prefixWord ++ tailWord_669550).sum := by decide
  have hdescent : baseEnd_669550 < baseStart_669550 := by decide
  rcases family_descends (prefixWord ++ tailWord_669550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669593 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_669593 : Nat := 118140960795 + 669593 * 2 ^ 59
def prefixEnd_669593 : Nat := 4983230072969 + 3 ^ 40 * 669593 * 2
def baseEnd_669593 : Nat := 229215367924069298672069

theorem tailTrace_669593 : CollatzResearch.WordTrace tailWord_669593 prefixEnd_669593 229215367924069298672069 := by
  unfold tailWord_669593
  simp only [CollatzResearch.WordTrace]
  refine ⟨24422063063186393225053433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16281375375457595483368955 24422063063186393225053433)
  ·
    refine ⟨18316547297389794918790075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24422063063186393225053433 18316547297389794918790075)
    ·
      refine ⟨27474820946084692378185113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18316547297389794918790075 27474820946084692378185113)
      ·
        refine ⟨20606115709563519283638835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27474820946084692378185113 20606115709563519283638835)
        ·
          refine ⟨30909173564345278925458253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20606115709563519283638835 30909173564345278925458253)
          ·
            refine ⟨11590940086629479597046845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30909173564345278925458253 11590940086629479597046845)
            ·
              refine ⟨4346602532486054848892567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11590940086629479597046845 4346602532486054848892567)
              ·
                refine ⟨6519903798729082273338851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4346602532486054848892567 6519903798729082273338851)
                ·
                  refine ⟨9779855698093623410008277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6519903798729082273338851 9779855698093623410008277)
                  ·
                    refine ⟨229215367924069298672069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9779855698093623410008277 229215367924069298672069)
                    ·
                      rfl

theorem cell22_669593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_669593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669593 prefixEnd_669593 := by exact prefixLift 669593
  have htrace : WordTrace (prefixWord ++ tailWord_669593) baseStart_669593 baseEnd_669593 := by
    simpa [prefixWord, tailWord_669593, baseEnd_669593] using wordTrace_append hprefix tailTrace_669593
  have hstable : (prefixWord ++ tailWord_669593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669593).length < 2 ^ (prefixWord ++ tailWord_669593).sum := by decide
  have hdescent : baseEnd_669593 < baseStart_669593 := by decide
  rcases family_descends (prefixWord ++ tailWord_669593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669623 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 10]
def baseStart_669623 : Nat := 118140960795 + 669623 * 2 ^ 59
def prefixEnd_669623 : Nat := 4983230072969 + 3 ^ 40 * 669623 * 2
def baseEnd_669623 : Nat := 76408545845719740140659

theorem tailTrace_669623 : CollatzResearch.WordTrace tailWord_669623 prefixEnd_669623 76408545845719740140659 := by
  unfold tailWord_669623
  simp only [CollatzResearch.WordTrace]
  refine ⟨24423157253077708348645523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16282104835385138899097015 24423157253077708348645523)
  ·
    refine ⟨36634735879616562522968285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24423157253077708348645523 36634735879616562522968285)
    ·
      refine ⟨13738025954856210946113107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36634735879616562522968285 13738025954856210946113107)
      ·
        refine ⟨20607038932284316419169661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13738025954856210946113107 20607038932284316419169661)
        ·
          refine ⟨7727639599606618657188623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20607038932284316419169661 7727639599606618657188623)
          ·
            refine ⟨11591459399409927985782935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7727639599606618657188623 11591459399409927985782935)
            ·
              refine ⟨17387189099114891978674403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11591459399409927985782935 17387189099114891978674403)
              ·
                refine ⟨26080783648672337968011605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17387189099114891978674403 26080783648672337968011605)
                ·
                  refine ⟨76408545845719740140659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 26080783648672337968011605 76408545845719740140659)
                  ·
                    rfl

theorem cell22_669623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 10].length) (baseStart_669623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669623 prefixEnd_669623 := by exact prefixLift 669623
  have htrace : WordTrace (prefixWord ++ tailWord_669623) baseStart_669623 baseEnd_669623 := by
    simpa [prefixWord, tailWord_669623, baseEnd_669623] using wordTrace_append hprefix tailTrace_669623
  have hstable : (prefixWord ++ tailWord_669623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669623).length < 2 ^ (prefixWord ++ tailWord_669623).sum := by decide
  have hdescent : baseEnd_669623 < baseStart_669623 := by decide
  rcases family_descends (prefixWord ++ tailWord_669623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669640 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 6]
def baseStart_669640 : Nat := 118140960795 + 669640 * 2 ^ 59
def prefixEnd_669640 : Nat := 4983230072969 + 3 ^ 40 * 669640 * 2
def baseEnd_669640 : Nat := 76410485661525614248975

theorem tailTrace_669640 : CollatzResearch.WordTrace tailWord_669640 prefixEnd_669640 76410485661525614248975 := by
  unfold tailWord_669640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211888647008060126007187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16282518196010746834676249 12211888647008060126007187)
  ·
    refine ⟨18317832970512090189010781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12211888647008060126007187 18317832970512090189010781)
    ·
      refine ⟨6869187363942033820879043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18317832970512090189010781 6869187363942033820879043)
      ·
        refine ⟨10303781045913050731318565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869187363942033820879043 10303781045913050731318565)
        ·
          refine ⟨1931958946108697012122231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10303781045913050731318565 1931958946108697012122231)
          ·
            refine ⟨2897938419163045518183347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931958946108697012122231 2897938419163045518183347)
            ·
              refine ⟨4346907628744568277275021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897938419163045518183347 4346907628744568277275021)
              ·
                refine ⟨1630090360779213103978133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4346907628744568277275021 1630090360779213103978133)
                ·
                  refine ⟨76410485661525614248975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1630090360779213103978133 76410485661525614248975)
                  ·
                    rfl

theorem cell22_669640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_669640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669640 prefixEnd_669640 := by exact prefixLift 669640
  have htrace : WordTrace (prefixWord ++ tailWord_669640) baseStart_669640 baseEnd_669640 := by
    simpa [prefixWord, tailWord_669640, baseEnd_669640] using wordTrace_append hprefix tailTrace_669640
  have hstable : (prefixWord ++ tailWord_669640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669640).length < 2 ^ (prefixWord ++ tailWord_669640).sum := by decide
  have hdescent : baseEnd_669640 < baseStart_669640 := by decide
  rcases family_descends (prefixWord ++ tailWord_669640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669751 : List Nat := [1, 1, 3, 1, 2, 2, 6, 2, 1, 3]
def baseStart_669751 : Nat := 118140960795 + 669751 * 2 ^ 59
def prefixEnd_669751 : Nat := 4983230072969 + 3 ^ 40 * 669751 * 2
def baseEnd_669751 : Nat := 229269454553009553221585

theorem tailTrace_669751 : CollatzResearch.WordTrace tailWord_669751 prefixEnd_669751 229269454553009553221585 := by
  unfold tailWord_669751
  simp only [CollatzResearch.WordTrace]
  refine ⟨24427825796613986209305107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16285217197742657472870071 24427825796613986209305107)
  ·
    refine ⟨36641738694920979313957661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24427825796613986209305107 36641738694920979313957661)
    ·
      refine ⟨13740652010595367242734123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36641738694920979313957661 13740652010595367242734123)
      ·
        refine ⟨20610978015893050864101185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13740652010595367242734123 20610978015893050864101185)
        ·
          refine ⟨15458233511919788148075889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20610978015893050864101185 15458233511919788148075889)
          ·
            refine ⟨11593675133939841111056917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15458233511919788148075889 11593675133939841111056917)
            ·
              refine ⟨543453521903430052080793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11593675133939841111056917 543453521903430052080793)
              ·
                refine ⟨407590141427572539060595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543453521903430052080793 407590141427572539060595)
                ·
                  refine ⟨611385212141358808590893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407590141427572539060595 611385212141358808590893)
                  ·
                    refine ⟨229269454553009553221585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 611385212141358808590893 229269454553009553221585)
                    ·
                      rfl

theorem cell22_669751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_669751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669751 prefixEnd_669751 := by exact prefixLift 669751
  have htrace : WordTrace (prefixWord ++ tailWord_669751) baseStart_669751 baseEnd_669751 := by
    simpa [prefixWord, tailWord_669751, baseEnd_669751] using wordTrace_append hprefix tailTrace_669751
  have hstable : (prefixWord ++ tailWord_669751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669751).length < 2 ^ (prefixWord ++ tailWord_669751).sum := by decide
  have hdescent : baseEnd_669751 < baseStart_669751 := by decide
  rcases family_descends (prefixWord ++ tailWord_669751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669775 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 6]
def baseStart_669775 : Nat := 118140960795 + 669775 * 2 ^ 59
def prefixEnd_669775 : Nat := 4983230072969 + 3 ^ 40 * 669775 * 2
def baseEnd_669775 : Nat := 76425890081160496873837

theorem tailTrace_669775 : CollatzResearch.WordTrace tailWord_669775 prefixEnd_669775 76425890081160496873837 := by
  unfold tailWord_669775
  simp only [CollatzResearch.WordTrace]
  refine ⟨24428701148527038308178779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16285800765684692205452519 24428701148527038308178779)
  ·
    refine ⟨36643051722790557462268169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24428701148527038308178779 36643051722790557462268169)
    ·
      refine ⟨27482288792092918096701127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36643051722790557462268169 27482288792092918096701127)
      ·
        refine ⟨41223433188139377145051691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27482288792092918096701127 41223433188139377145051691)
        ·
          refine ⟨61835149782209065717577537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41223433188139377145051691 61835149782209065717577537)
          ·
            refine ⟨46376362336656799288183153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61835149782209065717577537 46376362336656799288183153)
            ·
              refine ⟨34782271752492599466137365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46376362336656799288183153 34782271752492599466137365)
              ·
                refine ⟨1630418988398090599975189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34782271752492599466137365 1630418988398090599975189)
                ·
                  refine ⟨76425890081160496873837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1630418988398090599975189 76425890081160496873837)
                  ·
                    rfl

theorem cell22_669775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 6].length) (baseStart_669775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669775 prefixEnd_669775 := by exact prefixLift 669775
  have htrace : WordTrace (prefixWord ++ tailWord_669775) baseStart_669775 baseEnd_669775 := by
    simpa [prefixWord, tailWord_669775, baseEnd_669775] using wordTrace_append hprefix tailTrace_669775
  have hstable : (prefixWord ++ tailWord_669775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669775).length < 2 ^ (prefixWord ++ tailWord_669775).sum := by decide
  have hdescent : baseEnd_669775 < baseStart_669775 := by decide
  rcases family_descends (prefixWord ++ tailWord_669775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669777 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_669777 : Nat := 118140960795 + 669777 * 2 ^ 59
def prefixEnd_669777 : Nat := 4983230072969 + 3 ^ 40 * 669777 * 2
def baseEnd_669777 : Nat := 229278354884354152071505

theorem tailTrace_669777 : CollatzResearch.WordTrace tailWord_669777 prefixEnd_669777 229278354884354152071505 := by
  unfold tailWord_669777
  simp only [CollatzResearch.WordTrace]
  refine ⟨24428774094519792649751585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16285849396346528433167723 24428774094519792649751585)
  ·
    refine ⟨18321580570889844487313689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24428774094519792649751585 18321580570889844487313689)
    ·
      refine ⟨13741185428167383365485267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18321580570889844487313689 13741185428167383365485267)
      ·
        refine ⟨20611778142251075048227901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13741185428167383365485267 20611778142251075048227901)
        ·
          refine ⟨7729416803344153143085463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20611778142251075048227901 7729416803344153143085463)
          ·
            refine ⟨11594125205016229714628195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729416803344153143085463 11594125205016229714628195)
            ·
              refine ⟨17391187807524344571942293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11594125205016229714628195 17391187807524344571942293)
              ·
                refine ⟨815211928477703651809795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17391187807524344571942293 815211928477703651809795)
                ·
                  refine ⟨1222817892716555477714693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815211928477703651809795 1222817892716555477714693)
                  ·
                    refine ⟨229278354884354152071505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1222817892716555477714693 229278354884354152071505)
                    ·
                      rfl

theorem cell22_669777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_669777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669777 prefixEnd_669777 := by exact prefixLift 669777
  have htrace : WordTrace (prefixWord ++ tailWord_669777) baseStart_669777 baseEnd_669777 := by
    simpa [prefixWord, tailWord_669777, baseEnd_669777] using wordTrace_append hprefix tailTrace_669777
  have hstable : (prefixWord ++ tailWord_669777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669777).length < 2 ^ (prefixWord ++ tailWord_669777).sum := by decide
  have hdescent : baseEnd_669777 < baseStart_669777 := by decide
  rcases family_descends (prefixWord ++ tailWord_669777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_669961 : List Nat := [1, 2, 1, 1, 3, 5, 2, 3, 4]
def baseStart_669961 : Nat := 118140960795 + 669961 * 2 ^ 59
def prefixEnd_669961 : Nat := 4983230072969 + 3 ^ 40 * 669961 * 2
def baseEnd_669961 : Nat := 76447113948213001823647

theorem tailTrace_669961 : CollatzResearch.WordTrace tailWord_669961 prefixEnd_669961 76447113948213001823647 := by
  unfold tailWord_669961
  simp only [CollatzResearch.WordTrace]
  refine ⟨24435485125853192074449737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16290323417235461382966491 24435485125853192074449737)
  ·
    refine ⟨18326613844389894055837303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24435485125853192074449737 18326613844389894055837303)
    ·
      refine ⟨27489920766584841083755955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18326613844389894055837303 27489920766584841083755955)
      ·
        refine ⟨41234881149877261625633933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27489920766584841083755955 41234881149877261625633933)
        ·
          refine ⟨15463080431203973109612725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41234881149877261625633933 15463080431203973109612725)
          ·
            refine ⟨1449663790425372479026193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15463080431203973109612725 1449663790425372479026193)
            ·
              refine ⟨1087247842819029359269645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449663790425372479026193 1087247842819029359269645)
              ·
                refine ⟨407717941057136009726117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1087247842819029359269645 407717941057136009726117)
                ·
                  refine ⟨76447113948213001823647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407717941057136009726117 76447113948213001823647)
                  ·
                    rfl

theorem cell22_669961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 4].length) (baseStart_669961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_669961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_669961 prefixEnd_669961 := by exact prefixLift 669961
  have htrace : WordTrace (prefixWord ++ tailWord_669961) baseStart_669961 baseEnd_669961 := by
    simpa [prefixWord, tailWord_669961, baseEnd_669961] using wordTrace_append hprefix tailTrace_669961
  have hstable : (prefixWord ++ tailWord_669961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_669961).length < 2 ^ (prefixWord ++ tailWord_669961).sum := by decide
  have hdescent : baseEnd_669961 < baseStart_669961 := by decide
  rcases family_descends (prefixWord ++ tailWord_669961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670034 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_670034 : Nat := 118140960795 + 670034 * 2 ^ 59
def prefixEnd_670034 : Nat := 4983230072969 + 3 ^ 40 * 670034 * 2
def baseEnd_670034 : Nat := 76455443745497049465239

theorem tailTrace_670034 : CollatzResearch.WordTrace tailWord_670034 prefixEnd_670034 76455443745497049465239 := by
  unfold tailWord_670034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6109536913647181385464289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16292098436392483694571437 6109536913647181385464289)
  ·
    refine ⟨4582152685235386039098217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6109536913647181385464289 4582152685235386039098217)
    ·
      refine ⟨3436614513926539529323663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4582152685235386039098217 3436614513926539529323663)
      ·
        refine ⟨5154921770889809293985495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3436614513926539529323663 5154921770889809293985495)
        ·
          refine ⟨7732382656334713940978243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5154921770889809293985495 7732382656334713940978243)
          ·
            refine ⟨11598573984502070911467365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732382656334713940978243 11598573984502070911467365)
            ·
              refine ⟨2174732622094138295900131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11598573984502070911467365 2174732622094138295900131)
              ·
                refine ⟨3262098933141207443850197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2174732622094138295900131 3262098933141207443850197)
                ·
                  refine ⟨76455443745497049465239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3262098933141207443850197 76455443745497049465239)
                  ·
                    rfl

theorem cell22_670034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_670034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670034 prefixEnd_670034 := by exact prefixLift 670034
  have htrace : WordTrace (prefixWord ++ tailWord_670034) baseStart_670034 baseEnd_670034 := by
    simpa [prefixWord, tailWord_670034, baseEnd_670034] using wordTrace_append hprefix tailTrace_670034
  have hstable : (prefixWord ++ tailWord_670034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670034).length < 2 ^ (prefixWord ++ tailWord_670034).sum := by decide
  have hdescent : baseEnd_670034 < baseStart_670034 := by decide
  rcases family_descends (prefixWord ++ tailWord_670034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670044 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_670044 : Nat := 118140960795 + 670044 * 2 ^ 59
def prefixEnd_670044 : Nat := 4983230072969 + 3 ^ 40 * 670044 * 2
def baseEnd_670044 : Nat := 229369754440854455645687

theorem tailTrace_670044 : CollatzResearch.WordTrace tailWord_670044 prefixEnd_670044 229369754440854455645687 := by
  unfold tailWord_670044
  simp only [CollatzResearch.WordTrace]
  refine ⟨12219256192276248624860593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16292341589701664833147457 12219256192276248624860593)
  ·
    refine ⟨9164442144207186468645445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12219256192276248624860593 9164442144207186468645445)
    ·
      refine ⟨1718332902038847462871021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9164442144207186468645445 1718332902038847462871021)
      ·
        refine ⟨644374838264567798576633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1718332902038847462871021 644374838264567798576633)
        ·
          refine ⟨483281128698425848932475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644374838264567798576633 483281128698425848932475)
          ·
            refine ⟨724921693047638773398713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483281128698425848932475 724921693047638773398713)
            ·
              refine ⟨543691269785729080049035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724921693047638773398713 543691269785729080049035)
              ·
                refine ⟨815536904678593620073553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543691269785729080049035 815536904678593620073553)
                ·
                  refine ⟨611652678508945215055165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 815536904678593620073553 611652678508945215055165)
                  ·
                    refine ⟨229369754440854455645687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 611652678508945215055165 229369754440854455645687)
                    ·
                      rfl

theorem cell22_670044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_670044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670044 prefixEnd_670044 := by exact prefixLift 670044
  have htrace : WordTrace (prefixWord ++ tailWord_670044) baseStart_670044 baseEnd_670044 := by
    simpa [prefixWord, tailWord_670044, baseEnd_670044] using wordTrace_append hprefix tailTrace_670044
  have hstable : (prefixWord ++ tailWord_670044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670044).length < 2 ^ (prefixWord ++ tailWord_670044).sum := by decide
  have hdescent : baseEnd_670044 < baseStart_670044 := by decide
  rcases family_descends (prefixWord ++ tailWord_670044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670111 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 1, 5]
def baseStart_670111 : Nat := 118140960795 + 670111 * 2 ^ 59
def prefixEnd_670111 : Nat := 4983230072969 + 3 ^ 40 * 670111 * 2
def baseEnd_670111 : Nat := 229392689910088614220481

theorem tailTrace_670111 : CollatzResearch.WordTrace tailWord_670111 prefixEnd_670111 229392689910088614220481 := by
  unfold tailWord_670111
  simp only [CollatzResearch.WordTrace]
  refine ⟨24440956075309767692410187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16293970716873178461606791 24440956075309767692410187)
  ·
    refine ⟨36661434112964651538615281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24440956075309767692410187 36661434112964651538615281)
    ·
      refine ⟨27496075584723488653961461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36661434112964651538615281 27496075584723488653961461)
      ·
        refine ⟨2577757086067827061308887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27496075584723488653961461 2577757086067827061308887)
        ·
          refine ⟨3866635629101740591963331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577757086067827061308887 3866635629101740591963331)
          ·
            refine ⟨5799953443652610887944997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866635629101740591963331 5799953443652610887944997)
            ·
              refine ⟨1087491270684864541489687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5799953443652610887944997 1087491270684864541489687)
              ·
                refine ⟨1631236906027296812234531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087491270684864541489687 1631236906027296812234531)
                ·
                  refine ⟨2446855359040945218351797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631236906027296812234531 2446855359040945218351797)
                  ·
                    refine ⟨229392689910088614220481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2446855359040945218351797 229392689910088614220481)
                    ·
                      rfl

theorem cell22_670111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_670111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670111 prefixEnd_670111 := by exact prefixLift 670111
  have htrace : WordTrace (prefixWord ++ tailWord_670111) baseStart_670111 baseEnd_670111 := by
    simpa [prefixWord, tailWord_670111, baseEnd_670111] using wordTrace_append hprefix tailTrace_670111
  have hstable : (prefixWord ++ tailWord_670111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670111).length < 2 ^ (prefixWord ++ tailWord_670111).sum := by decide
  have hdescent : baseEnd_670111 < baseStart_670111 := by decide
  rcases family_descends (prefixWord ++ tailWord_670111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670113 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 6]
def baseStart_670113 : Nat := 118140960795 + 670113 * 2 ^ 59
def prefixEnd_670113 : Nat := 4983230072969 + 3 ^ 40 * 670113 * 2
def baseEnd_670113 : Nat := 76464458183653758556825

theorem tailTrace_670113 : CollatzResearch.WordTrace tailWord_670113 prefixEnd_670113 76464458183653758556825 := by
  unfold tailWord_670113
  simp only [CollatzResearch.WordTrace]
  refine ⟨24441029021302522033982993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16294019347535014689321995 24441029021302522033982993)
  ·
    refine ⟨18330771765976891525487245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24441029021302522033982993 18330771765976891525487245)
    ·
      refine ⟨6874039412241334322057717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18330771765976891525487245 6874039412241334322057717)
      ·
        refine ⟨644441194897625092692911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6874039412241334322057717 644441194897625092692911)
        ·
          refine ⟨966661792346437639039367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644441194897625092692911 966661792346437639039367)
          ·
            refine ⟨1449992688519656458559051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966661792346437639039367 1449992688519656458559051)
            ·
              refine ⟨2174989032779484687838577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449992688519656458559051 2174989032779484687838577)
              ·
                refine ⟨1631241774584613515878933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2174989032779484687838577 1631241774584613515878933)
                ·
                  refine ⟨76464458183653758556825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1631241774584613515878933 76464458183653758556825)
                  ·
                    rfl

theorem cell22_670113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_670113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670113 prefixEnd_670113 := by exact prefixLift 670113
  have htrace : WordTrace (prefixWord ++ tailWord_670113) baseStart_670113 baseEnd_670113 := by
    simpa [prefixWord, tailWord_670113, baseEnd_670113] using wordTrace_append hprefix tailTrace_670113
  have hstable : (prefixWord ++ tailWord_670113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670113).length < 2 ^ (prefixWord ++ tailWord_670113).sum := by decide
  have hdescent : baseEnd_670113 < baseStart_670113 := by decide
  rcases family_descends (prefixWord ++ tailWord_670113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670132 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_670132 : Nat := 118140960795 + 670132 * 2 ^ 59
def prefixEnd_670132 : Nat := 4983230072969 + 3 ^ 40 * 670132 * 2
def baseEnd_670132 : Nat := 229399878639251559445417

theorem tailTrace_670132 : CollatzResearch.WordTrace tailWord_670132 prefixEnd_670132 229399878639251559445417 := by
  unfold tailWord_670132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12220861004116844139462325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16294481338822458852616433 12220861004116844139462325)
  ·
    refine ⟨1145705719135954138074593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12220861004116844139462325 1145705719135954138074593)
    ·
      refine ⟨859279289351965603555945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1145705719135954138074593 859279289351965603555945)
      ·
        refine ⟨644459467013974202666959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 859279289351965603555945 644459467013974202666959)
        ·
          refine ⟨966689200520961304000439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644459467013974202666959 966689200520961304000439)
          ·
            refine ⟨1450033800781441956000659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966689200520961304000439 1450033800781441956000659)
            ·
              refine ⟨2175050701172162934000989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450033800781441956000659 2175050701172162934000989)
              ·
                refine ⟨815644012939561100250371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2175050701172162934000989 815644012939561100250371)
                ·
                  refine ⟨1223466019409341650375557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815644012939561100250371 1223466019409341650375557)
                  ·
                    refine ⟨229399878639251559445417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1223466019409341650375557 229399878639251559445417)
                    ·
                      rfl

theorem cell22_670132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_670132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670132 prefixEnd_670132 := by exact prefixLift 670132
  have htrace : WordTrace (prefixWord ++ tailWord_670132) baseStart_670132 baseEnd_670132 := by
    simpa [prefixWord, tailWord_670132, baseEnd_670132] using wordTrace_append hprefix tailTrace_670132
  have hstable : (prefixWord ++ tailWord_670132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670132).length < 2 ^ (prefixWord ++ tailWord_670132).sum := by decide
  have hdescent : baseEnd_670132 < baseStart_670132 := by decide
  rcases family_descends (prefixWord ++ tailWord_670132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670162 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_670162 : Nat := 118140960795 + 670162 * 2 ^ 59
def prefixEnd_670162 : Nat := 4983230072969 + 3 ^ 40 * 670162 * 2
def baseEnd_670162 : Nat := 229410148252341481195325

theorem tailTrace_670162 : CollatzResearch.WordTrace tailWord_670162 prefixEnd_670162 229410148252341481195325 := by
  unfold tailWord_670162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6110704049531250850629185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16295210798750002268344493 6110704049531250850629185)
  ·
    refine ⟨4583028037148438137971889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6110704049531250850629185 4583028037148438137971889)
    ·
      refine ⟨3437271027861328603478917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4583028037148438137971889 3437271027861328603478917)
      ·
        refine ⟨644488317723999113152297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3437271027861328603478917 644488317723999113152297)
        ·
          refine ⟨483366238292999334864223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644488317723999113152297 483366238292999334864223)
          ·
            refine ⟨725049357439499002296335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483366238292999334864223 725049357439499002296335)
            ·
              refine ⟨1087574036159248503444503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725049357439499002296335 1087574036159248503444503)
              ·
                refine ⟨1631361054238872755166755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087574036159248503444503 1631361054238872755166755)
                ·
                  refine ⟨2447041581358309132750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631361054238872755166755 2447041581358309132750133)
                  ·
                    refine ⟨229410148252341481195325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2447041581358309132750133 229410148252341481195325)
                    ·
                      rfl

theorem cell22_670162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_670162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670162 prefixEnd_670162 := by exact prefixLift 670162
  have htrace : WordTrace (prefixWord ++ tailWord_670162) baseStart_670162 baseEnd_670162 := by
    simpa [prefixWord, tailWord_670162, baseEnd_670162] using wordTrace_append hprefix tailTrace_670162
  have hstable : (prefixWord ++ tailWord_670162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670162).length < 2 ^ (prefixWord ++ tailWord_670162).sum := by decide
  have hdescent : baseEnd_670162 < baseStart_670162 := by decide
  rcases family_descends (prefixWord ++ tailWord_670162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670173 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_670173 : Nat := 118140960795 + 670173 * 2 ^ 59
def prefixEnd_670173 : Nat := 4983230072969 + 3 ^ 40 * 670173 * 2
def baseEnd_670173 : Nat := 229413913777141119170291

theorem tailTrace_670173 : CollatzResearch.WordTrace tailWord_670173 prefixEnd_670173 229413913777141119170291 := by
  unfold tailWord_670173
  simp only [CollatzResearch.WordTrace]
  refine ⟨24443217401085152281167173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16295478267390101520778115 24443217401085152281167173)
  ·
    refine ⟨4583103262703466052718845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24443217401085152281167173 4583103262703466052718845)
    ·
      refine ⟨1718663723513799769769567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4583103262703466052718845 1718663723513799769769567)
      ·
        refine ⟨2577995585270699654654351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718663723513799769769567 2577995585270699654654351)
        ·
          refine ⟨3866993377906049481981527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577995585270699654654351 3866993377906049481981527)
          ·
            refine ⟨5800490066859074222972291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866993377906049481981527 5800490066859074222972291)
            ·
              refine ⟨8700735100288611334458437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800490066859074222972291 8700735100288611334458437)
              ·
                refine ⟨1631387831304114625210957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8700735100288611334458437 1631387831304114625210957)
                ·
                  refine ⟨611770436739042984454109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1631387831304114625210957 611770436739042984454109)
                  ·
                    refine ⟨229413913777141119170291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 611770436739042984454109 229413913777141119170291)
                    ·
                      rfl

theorem cell22_670173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_670173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670173 prefixEnd_670173 := by exact prefixLift 670173
  have htrace : WordTrace (prefixWord ++ tailWord_670173) baseStart_670173 baseEnd_670173 := by
    simpa [prefixWord, tailWord_670173, baseEnd_670173] using wordTrace_append hprefix tailTrace_670173
  have hstable : (prefixWord ++ tailWord_670173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670173).length < 2 ^ (prefixWord ++ tailWord_670173).sum := by decide
  have hdescent : baseEnd_670173 < baseStart_670173 := by decide
  rcases family_descends (prefixWord ++ tailWord_670173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670186 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_670186 : Nat := 118140960795 + 670186 * 2 ^ 59
def prefixEnd_670186 : Nat := 4983230072969 + 3 ^ 40 * 670186 * 2
def baseEnd_670186 : Nat := 76472787980937806198417

theorem tailTrace_670186 : CollatzResearch.WordTrace tailWord_670186 prefixEnd_670186 76472787980937806198417 := by
  unfold tailWord_670186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6110922887509513875347603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16295794366692037000926941 6110922887509513875347603)
  ·
    refine ⟨9166384331264270813021405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6110922887509513875347603 9166384331264270813021405)
    ·
      refine ⟨3437394124224101554883027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9166384331264270813021405 3437394124224101554883027)
      ·
        refine ⟨5156091186336152332324541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3437394124224101554883027 5156091186336152332324541)
        ·
          refine ⟨1933534194876057124621703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5156091186336152332324541 1933534194876057124621703)
          ·
            refine ⟨2900301292314085686932555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933534194876057124621703 2900301292314085686932555)
            ·
              refine ⟨4350451938471128530398833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900301292314085686932555 4350451938471128530398833)
              ·
                refine ⟨3262838953853346397799125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4350451938471128530398833 3262838953853346397799125)
                ·
                  refine ⟨76472787980937806198417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3262838953853346397799125 76472787980937806198417)
                  ·
                    rfl

theorem cell22_670186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_670186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670186 prefixEnd_670186 := by exact prefixLift 670186
  have htrace : WordTrace (prefixWord ++ tailWord_670186) baseStart_670186 baseEnd_670186 := by
    simpa [prefixWord, tailWord_670186, baseEnd_670186] using wordTrace_append hprefix tailTrace_670186
  have hstable : (prefixWord ++ tailWord_670186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670186).length < 2 ^ (prefixWord ++ tailWord_670186).sum := by decide
  have hdescent : baseEnd_670186 < baseStart_670186 := by decide
  rcases family_descends (prefixWord ++ tailWord_670186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670199 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 10]
def baseStart_670199 : Nat := 118140960795 + 670199 * 2 ^ 59
def prefixEnd_670199 : Nat := 4983230072969 + 3 ^ 40 * 670199 * 2
def baseEnd_670199 : Nat := 229422814108485718020211

theorem tailTrace_670199 : CollatzResearch.WordTrace tailWord_670199 prefixEnd_670199 229422814108485718020211 := by
  unfold tailWord_670199
  simp only [CollatzResearch.WordTrace]
  refine ⟨24444165698990958721613651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16296110465993972481075767 24444165698990958721613651)
  ·
    refine ⟨36666248548486438082420477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24444165698990958721613651 36666248548486438082420477)
    ·
      refine ⟨13749843205682414280907679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36666248548486438082420477 13749843205682414280907679)
      ·
        refine ⟨20624764808523621421361519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13749843205682414280907679 20624764808523621421361519)
        ·
          refine ⟨30937147212785432132042279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20624764808523621421361519 30937147212785432132042279)
          ·
            refine ⟨46405720819178148198063419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30937147212785432132042279 46405720819178148198063419)
            ·
              refine ⟨69608581228767222297095129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46405720819178148198063419 69608581228767222297095129)
              ·
                refine ⟨52206435921575416722821347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69608581228767222297095129 52206435921575416722821347)
                ·
                  refine ⟨78309653882363125084232021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52206435921575416722821347 78309653882363125084232021)
                  ·
                    refine ⟨229422814108485718020211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 78309653882363125084232021 229422814108485718020211)
                    ·
                      rfl

theorem cell22_670199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_670199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670199 prefixEnd_670199 := by exact prefixLift 670199
  have htrace : WordTrace (prefixWord ++ tailWord_670199) baseStart_670199 baseEnd_670199 := by
    simpa [prefixWord, tailWord_670199, baseEnd_670199] using wordTrace_append hprefix tailTrace_670199
  have hstable : (prefixWord ++ tailWord_670199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670199).length < 2 ^ (prefixWord ++ tailWord_670199).sum := by decide
  have hdescent : baseEnd_670199 < baseStart_670199 := by decide
  rcases family_descends (prefixWord ++ tailWord_670199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670216 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_670216 : Nat := 118140960795 + 670216 * 2 ^ 59
def prefixEnd_670216 : Nat := 4983230072969 + 3 ^ 40 * 670216 * 2
def baseEnd_670216 : Nat := 229428633555903340345159

theorem tailTrace_670216 : CollatzResearch.WordTrace tailWord_670216 prefixEnd_670216 229428633555903340345159 := by
  unfold tailWord_670216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222392869964685312491251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16296523826619580416655001 12222392869964685312491251)
  ·
    refine ⟨18333589304947027968736877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12222392869964685312491251 18333589304947027968736877)
    ·
      refine ⟨6875095989355135488276329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18333589304947027968736877 6875095989355135488276329)
      ·
        refine ⟨5156321992016351616207247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6875095989355135488276329 5156321992016351616207247)
        ·
          refine ⟨7734482988024527424310871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5156321992016351616207247 7734482988024527424310871)
          ·
            refine ⟨11601724482036791136466307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7734482988024527424310871 11601724482036791136466307)
            ·
              refine ⟨17402586723055186704699461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11601724482036791136466307 17402586723055186704699461)
              ·
                refine ⟨3262985010572847507131149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17402586723055186704699461 3262985010572847507131149)
                ·
                  refine ⟨1223619378964817815174181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3262985010572847507131149 1223619378964817815174181)
                  ·
                    refine ⟨229428633555903340345159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1223619378964817815174181 229428633555903340345159)
                    ·
                      rfl

theorem cell22_670216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_670216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670216 prefixEnd_670216 := by exact prefixLift 670216
  have htrace : WordTrace (prefixWord ++ tailWord_670216) baseStart_670216 baseEnd_670216 := by
    simpa [prefixWord, tailWord_670216, baseEnd_670216] using wordTrace_append hprefix tailTrace_670216
  have hstable : (prefixWord ++ tailWord_670216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670216).length < 2 ^ (prefixWord ++ tailWord_670216).sum := by decide
  have hdescent : baseEnd_670216 < baseStart_670216 := by decide
  rcases family_descends (prefixWord ++ tailWord_670216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670220 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 5]
def baseStart_670220 : Nat := 118140960795 + 670220 * 2 ^ 59
def prefixEnd_670220 : Nat := 4983230072969 + 3 ^ 40 * 670220 * 2
def baseEnd_670220 : Nat := 76476667612549554415049

theorem tailTrace_670220 : CollatzResearch.WordTrace tailWord_670220 prefixEnd_670220 76476667612549554415049 := by
  unfold tailWord_670220
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222465815957439654064057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16296621087943252872085409 12222465815957439654064057)
  ·
    refine ⟨9166849361968079740548043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12222465815957439654064057 9166849361968079740548043)
    ·
      refine ⟨13750274042952119610822065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9166849361968079740548043 13750274042952119610822065)
      ·
        refine ⟨10312705532214089708116549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13750274042952119610822065 10312705532214089708116549)
        ·
          refine ⟨1933632287290141820271853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10312705532214089708116549 1933632287290141820271853)
          ·
            refine ⟨725112107733803182601945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1933632287290141820271853 725112107733803182601945)
            ·
              refine ⟨543834080800352386951459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725112107733803182601945 543834080800352386951459)
              ·
                refine ⟨815751121200528580427189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543834080800352386951459 815751121200528580427189)
                ·
                  refine ⟨76476667612549554415049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 815751121200528580427189 76476667612549554415049)
                  ·
                    rfl

theorem cell22_670220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_670220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670220 prefixEnd_670220 := by exact prefixLift 670220
  have htrace : WordTrace (prefixWord ++ tailWord_670220) baseStart_670220 baseEnd_670220 := by
    simpa [prefixWord, tailWord_670220, baseEnd_670220] using wordTrace_append hprefix tailTrace_670220
  have hstable : (prefixWord ++ tailWord_670220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670220).length < 2 ^ (prefixWord ++ tailWord_670220).sum := by decide
  have hdescent : baseEnd_670220 < baseStart_670220 := by decide
  rcases family_descends (prefixWord ++ tailWord_670220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670308 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_670308 : Nat := 118140960795 + 670308 * 2 ^ 59
def prefixEnd_670308 : Nat := 4983230072969 + 3 ^ 40 * 670308 * 2
def baseEnd_670308 : Nat := 229460127036045767044877

theorem tailTrace_670308 : CollatzResearch.WordTrace tailWord_670308 prefixEnd_670308 229460127036045767044877 := by
  unfold tailWord_670308
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224070627798035168665789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16298760837064046891554385 12224070627798035168665789)
  ·
    refine ⟨4584026485424263188249671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12224070627798035168665789 4584026485424263188249671)
    ·
      refine ⟨6876039728136394782374507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584026485424263188249671 6876039728136394782374507)
      ·
        refine ⟨10314059592204592173561761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876039728136394782374507 10314059592204592173561761)
        ·
          refine ⟨7735544694153444130171321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10314059592204592173561761 7735544694153444130171321)
          ·
            refine ⟨5801658520615083097628491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7735544694153444130171321 5801658520615083097628491)
            ·
              refine ⟨8702487780922624646442737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801658520615083097628491 8702487780922624646442737)
              ·
                refine ⟨6526865835691968484832053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8702487780922624646442737 6526865835691968484832053)
                ·
                  refine ⟨611893672096122045453005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6526865835691968484832053 611893672096122045453005)
                  ·
                    refine ⟨229460127036045767044877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 611893672096122045453005 229460127036045767044877)
                    ·
                      rfl

theorem cell22_670308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_670308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670308 prefixEnd_670308 := by exact prefixLift 670308
  have htrace : WordTrace (prefixWord ++ tailWord_670308) baseStart_670308 baseEnd_670308 := by
    simpa [prefixWord, tailWord_670308, baseEnd_670308] using wordTrace_append hprefix tailTrace_670308
  have hstable : (prefixWord ++ tailWord_670308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670308).length < 2 ^ (prefixWord ++ tailWord_670308).sum := by decide
  have hdescent : baseEnd_670308 < baseStart_670308 := by decide
  rcases family_descends (prefixWord ++ tailWord_670308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670383 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 6]
def baseStart_670383 : Nat := 118140960795 + 670383 * 2 ^ 59
def prefixEnd_670383 : Nat := 4983230072969 + 3 ^ 40 * 670383 * 2
def baseEnd_670383 : Nat := 76495267022923523806549

theorem tailTrace_670383 : CollatzResearch.WordTrace tailWord_670383 prefixEnd_670383 76495267022923523806549 := by
  unfold tailWord_670383
  simp only [CollatzResearch.WordTrace]
  refine ⟨24450876730324358146311803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16300584486882905430874535 24450876730324358146311803)
  ·
    refine ⟨36676315095486537219467705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24450876730324358146311803 36676315095486537219467705)
    ·
      refine ⟨27507236321614902914600779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36676315095486537219467705 27507236321614902914600779)
      ·
        refine ⟨41260854482422354371901169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27507236321614902914600779 41260854482422354371901169)
        ·
          refine ⟨30945640861816765778925877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41260854482422354371901169 30945640861816765778925877)
          ·
            refine ⟨2901153830795321791774301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30945640861816765778925877 2901153830795321791774301)
            ·
              refine ⟨1087932686548245671915363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2901153830795321791774301 1087932686548245671915363)
              ·
                refine ⟨1631899029822368507873045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087932686548245671915363 1631899029822368507873045)
                ·
                  refine ⟨76495267022923523806549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1631899029822368507873045 76495267022923523806549)
                  ·
                    rfl

theorem cell22_670383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 6].length) (baseStart_670383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670383 prefixEnd_670383 := by exact prefixLift 670383
  have htrace : WordTrace (prefixWord ++ tailWord_670383) baseStart_670383 baseEnd_670383 := by
    simpa [prefixWord, tailWord_670383, baseEnd_670383] using wordTrace_append hprefix tailTrace_670383
  have hstable : (prefixWord ++ tailWord_670383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670383).length < 2 ^ (prefixWord ++ tailWord_670383).sum := by decide
  have hdescent : baseEnd_670383 < baseStart_670383 := by decide
  rcases family_descends (prefixWord ++ tailWord_670383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670460 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_670460 : Nat := 118140960795 + 670460 * 2 ^ 59
def prefixEnd_670460 : Nat := 4983230072969 + 3 ^ 40 * 670460 * 2
def baseEnd_670460 : Nat := 229512159742368037244411

theorem tailTrace_670460 : CollatzResearch.WordTrace tailWord_670460 prefixEnd_670460 229512159742368037244411 := by
  unfold tailWord_670460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12226842575522700148432417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16302456767363600197909889 12226842575522700148432417)
  ·
    refine ⟨9170131931642025111324313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12226842575522700148432417 9170131931642025111324313)
    ·
      refine ⟨6877598948731518833493235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9170131931642025111324313 6877598948731518833493235)
      ·
        refine ⟨10316398423097278250239853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6877598948731518833493235 10316398423097278250239853)
        ·
          refine ⟨3868649408661479343839945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10316398423097278250239853 3868649408661479343839945)
          ·
            refine ⟨2901487056496109507879959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3868649408661479343839945 2901487056496109507879959)
            ·
              refine ⟨4352230584744164261819939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901487056496109507879959 4352230584744164261819939)
              ·
                refine ⟨6528345877116246392729909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352230584744164261819939 6528345877116246392729909)
                ·
                  refine ⟨612032425979648099318429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6528345877116246392729909 612032425979648099318429)
                  ·
                    refine ⟨229512159742368037244411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 612032425979648099318429 229512159742368037244411)
                    ·
                      rfl

theorem cell22_670460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_670460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670460 prefixEnd_670460 := by exact prefixLift 670460
  have htrace : WordTrace (prefixWord ++ tailWord_670460) baseStart_670460 baseEnd_670460 := by
    simpa [prefixWord, tailWord_670460, baseEnd_670460] using wordTrace_append hprefix tailTrace_670460
  have hstable : (prefixWord ++ tailWord_670460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670460).length < 2 ^ (prefixWord ++ tailWord_670460).sum := by decide
  have hdescent : baseEnd_670460 < baseStart_670460 := by decide
  rcases family_descends (prefixWord ++ tailWord_670460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670462 : List Nat := [4, 2, 2, 1, 2, 2, 3, 6]
def baseStart_670462 : Nat := 118140960795 + 670462 * 2 ^ 59
def prefixEnd_670462 : Nat := 4983230072969 + 3 ^ 40 * 670462 * 2
def baseEnd_670462 : Nat := 25501427153693410966045

theorem tailTrace_670462 : CollatzResearch.WordTrace tailWord_670462 prefixEnd_670462 25501427153693410966045 := by
  unfold tailWord_670462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3056719762129769329804705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16302505398025436425625093 3056719762129769329804705)
  ·
    refine ⟨2292539821597326997353529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3056719762129769329804705 2292539821597326997353529)
    ·
      refine ⟨1719404866197995248015147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2292539821597326997353529 1719404866197995248015147)
      ·
        refine ⟨2579107299296992872022721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1719404866197995248015147 2579107299296992872022721)
        ·
          refine ⟨1934330474472744654017041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2579107299296992872022721 1934330474472744654017041)
          ·
            refine ⟨1450747855854558490512781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1934330474472744654017041 1450747855854558490512781)
            ·
              refine ⟨544030445945459433942293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1450747855854558490512781 544030445945459433942293)
              ·
                refine ⟨25501427153693410966045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 544030445945459433942293 25501427153693410966045)
                ·
                  rfl

theorem cell22_670462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_670462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670462 prefixEnd_670462 := by exact prefixLift 670462
  have htrace : WordTrace (prefixWord ++ tailWord_670462) baseStart_670462 baseEnd_670462 := by
    simpa [prefixWord, tailWord_670462, baseEnd_670462] using wordTrace_append hprefix tailTrace_670462
  have hstable : (prefixWord ++ tailWord_670462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670462).length < 2 ^ (prefixWord ++ tailWord_670462).sum := by decide
  have hdescent : baseEnd_670462 < baseStart_670462 := by decide
  rcases family_descends (prefixWord ++ tailWord_670462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670655 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 5, 4]
def baseStart_670655 : Nat := 118140960795 + 670655 * 2 ^ 59
def prefixEnd_670655 : Nat := 4983230072969 + 3 ^ 40 * 670655 * 2
def baseEnd_670655 : Nat := 229578912227452528618813

theorem tailTrace_670655 : CollatzResearch.WordTrace tailWord_670655 prefixEnd_670655 229578912227452528618813 := by
  unfold tailWord_670655
  simp only [CollatzResearch.WordTrace]
  refine ⟨24460797385338948600213419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16307198256892632400142279 24460797385338948600213419)
  ·
    refine ⟨36691196078008422900320129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24460797385338948600213419 36691196078008422900320129)
    ·
      refine ⟨27518397058506317175240097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36691196078008422900320129 27518397058506317175240097)
      ·
        refine ⟨20638797793879737881430073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27518397058506317175240097 20638797793879737881430073)
        ·
          refine ⟨15479098345409803411072555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20638797793879737881430073 15479098345409803411072555)
          ·
            refine ⟨23218647518114705116608833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15479098345409803411072555 23218647518114705116608833)
            ·
              refine ⟨17413985638586028837456625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23218647518114705116608833 17413985638586028837456625)
              ·
                refine ⟨13060489228939521628092469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17413985638586028837456625 13060489228939521628092469)
                ·
                  refine ⟨1224420865213080152633669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13060489228939521628092469 1224420865213080152633669)
                  ·
                    refine ⟨229578912227452528618813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1224420865213080152633669 229578912227452528618813)
                    ·
                      rfl

theorem cell22_670655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_670655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670655 prefixEnd_670655 := by exact prefixLift 670655
  have htrace : WordTrace (prefixWord ++ tailWord_670655) baseStart_670655 baseEnd_670655 := by
    simpa [prefixWord, tailWord_670655, baseEnd_670655] using wordTrace_append hprefix tailTrace_670655
  have hstable : (prefixWord ++ tailWord_670655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670655).length < 2 ^ (prefixWord ++ tailWord_670655).sum := by decide
  have hdescent : baseEnd_670655 < baseStart_670655 := by decide
  rcases family_descends (prefixWord ++ tailWord_670655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670721 : List Nat := [1, 2, 4, 1, 2, 3, 3, 2, 4]
def baseStart_670721 : Nat := 118140960795 + 670721 * 2 ^ 59
def prefixEnd_670721 : Nat := 4983230072969 + 3 ^ 40 * 670721 * 2
def baseEnd_670721 : Nat := 76533835125416785489537

theorem tailTrace_670721 : CollatzResearch.WordTrace tailWord_670721 prefixEnd_670721 76533835125416785489537 := by
  unfold tailWord_670721
  simp only [CollatzResearch.WordTrace]
  refine ⟨24463204603099841872116017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16308803068733227914744011 24463204603099841872116017)
  ·
    refine ⟨18347403452324881404087013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24463204603099841872116017 18347403452324881404087013)
    ·
      refine ⟨3440138147310915263266315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18347403452324881404087013 3440138147310915263266315)
      ·
        refine ⟨5160207220966372894899473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3440138147310915263266315 5160207220966372894899473)
        ·
          refine ⟨3870155415724779671174605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5160207220966372894899473 3870155415724779671174605)
          ·
            refine ⟨1451308280896792376690477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3870155415724779671174605 1451308280896792376690477)
            ·
              refine ⟨544240605336297141258929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451308280896792376690477 544240605336297141258929)
              ·
                refine ⟨408180454002222855944197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544240605336297141258929 408180454002222855944197)
                ·
                  refine ⟨76533835125416785489537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408180454002222855944197 76533835125416785489537)
                  ·
                    rfl

theorem cell22_670721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 4].length) (baseStart_670721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670721 prefixEnd_670721 := by exact prefixLift 670721
  have htrace : WordTrace (prefixWord ++ tailWord_670721) baseStart_670721 baseEnd_670721 := by
    simpa [prefixWord, tailWord_670721, baseEnd_670721] using wordTrace_append hprefix tailTrace_670721
  have hstable : (prefixWord ++ tailWord_670721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670721).length < 2 ^ (prefixWord ++ tailWord_670721).sum := by decide
  have hdescent : baseEnd_670721 < baseStart_670721 := by decide
  rcases family_descends (prefixWord ++ tailWord_670721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670732 : List Nat := [2, 2, 1, 2, 3, 3, 2, 7]
def baseStart_670732 : Nat := 118140960795 + 670732 * 2 ^ 59
def prefixEnd_670732 : Nat := 4983230072969 + 3 ^ 40 * 670732 * 2
def baseEnd_670732 : Nat := 25511696766783332715953

theorem tailTrace_670732 : CollatzResearch.WordTrace tailWord_670732 prefixEnd_670732 25511696766783332715953 := by
  unfold tailWord_670732
  simp only [CollatzResearch.WordTrace]
  refine ⟨12231802903029995375383225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16309070537373327167177633 12231802903029995375383225)
  ·
    refine ⟨9173852177272496531537419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12231802903029995375383225 9173852177272496531537419)
    ·
      refine ⟨13760778265908744797306129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9173852177272496531537419 13760778265908744797306129)
      ·
        refine ⟨10320583699431558597979597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13760778265908744797306129 10320583699431558597979597)
        ·
          refine ⟨3870218887286834474242349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10320583699431558597979597 3870218887286834474242349)
          ·
            refine ⟨1451332082732562927840881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3870218887286834474242349 1451332082732562927840881)
            ·
              refine ⟨1088499062049422195880661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451332082732562927840881 1088499062049422195880661)
              ·
                refine ⟨25511696766783332715953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1088499062049422195880661 25511696766783332715953)
                ·
                  rfl

theorem cell22_670732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 7].length) (baseStart_670732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670732 prefixEnd_670732 := by exact prefixLift 670732
  have htrace : WordTrace (prefixWord ++ tailWord_670732) baseStart_670732 baseEnd_670732 := by
    simpa [prefixWord, tailWord_670732, baseEnd_670732] using wordTrace_append hprefix tailTrace_670732
  have hstable : (prefixWord ++ tailWord_670732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670732).length < 2 ^ (prefixWord ++ tailWord_670732).sum := by decide
  have hdescent : baseEnd_670732 < baseStart_670732 := by decide
  rcases family_descends (prefixWord ++ tailWord_670732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670792 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_670792 : Nat := 118140960795 + 670792 * 2 ^ 59
def prefixEnd_670792 : Nat := 4983230072969 + 3 ^ 40 * 670792 * 2
def baseEnd_670792 : Nat := 229625810127229837943393

theorem tailTrace_670792 : CollatzResearch.WordTrace tailWord_670792 prefixEnd_670792 229625810127229837943393 := by
  unfold tailWord_670792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12232897092921310498975315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16310529457228413998633753 12232897092921310498975315)
  ·
    refine ⟨18349345639381965748462973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12232897092921310498975315 18349345639381965748462973)
    ·
      refine ⟨6881004614768237155673615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18349345639381965748462973 6881004614768237155673615)
      ·
        refine ⟨10321506922152355733510423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6881004614768237155673615 10321506922152355733510423)
        ·
          refine ⟨15482260383228533600265635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10321506922152355733510423 15482260383228533600265635)
          ·
            refine ⟨23223390574842800400398453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15482260383228533600265635 23223390574842800400398453)
            ·
              refine ⟨2177192866391512537537355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23223390574842800400398453 2177192866391512537537355)
              ·
                refine ⟨3265789299587268806306033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177192866391512537537355 3265789299587268806306033)
                ·
                  refine ⟨2449341974690451604729525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265789299587268806306033 2449341974690451604729525)
                  ·
                    refine ⟨229625810127229837943393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2449341974690451604729525 229625810127229837943393)
                    ·
                      rfl

theorem cell22_670792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_670792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670792 prefixEnd_670792 := by exact prefixLift 670792
  have htrace : WordTrace (prefixWord ++ tailWord_670792) baseStart_670792 baseEnd_670792 := by
    simpa [prefixWord, tailWord_670792, baseEnd_670792] using wordTrace_append hprefix tailTrace_670792
  have hstable : (prefixWord ++ tailWord_670792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670792).length < 2 ^ (prefixWord ++ tailWord_670792).sum := by decide
  have hdescent : baseEnd_670792 < baseStart_670792 := by decide
  rcases family_descends (prefixWord ++ tailWord_670792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670839 : List Nat := [1, 1, 3, 1, 1, 4, 1, 6, 4]
def baseStart_670839 : Nat := 118140960795 + 670839 * 2 ^ 59
def prefixEnd_670839 : Nat := 4983230072969 + 3 ^ 40 * 670839 * 2
def baseEnd_670839 : Nat := 76547299729245794006083

theorem tailTrace_670839 : CollatzResearch.WordTrace tailWord_670839 prefixEnd_670839 76547299729245794006083 := by
  unfold tailWord_670839
  simp only [CollatzResearch.WordTrace]
  refine ⟨24467508416672348024911571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16311672277781565349941047 24467508416672348024911571)
  ·
    refine ⟨36701262625008522037367357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24467508416672348024911571 36701262625008522037367357)
    ·
      refine ⟨13762973484378195764012759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36701262625008522037367357 13762973484378195764012759)
      ·
        refine ⟨20644460226567293646019139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13762973484378195764012759 20644460226567293646019139)
        ·
          refine ⟨30966690339850940469028709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20644460226567293646019139 30966690339850940469028709)
          ·
            refine ⟨5806254438722051337942883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30966690339850940469028709 5806254438722051337942883)
            ·
              refine ⟨8709381658083077006914325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5806254438722051337942883 8709381658083077006914325)
              ·
                refine ⟨408252265222644234699109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8709381658083077006914325 408252265222644234699109)
                ·
                  refine ⟨76547299729245794006083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408252265222644234699109 76547299729245794006083)
                  ·
                    rfl

theorem cell22_670839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 4].length) (baseStart_670839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670839 prefixEnd_670839 := by exact prefixLift 670839
  have htrace : WordTrace (prefixWord ++ tailWord_670839) baseStart_670839 baseEnd_670839 := by
    simpa [prefixWord, tailWord_670839, baseEnd_670839] using wordTrace_append hprefix tailTrace_670839
  have hstable : (prefixWord ++ tailWord_670839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670839).length < 2 ^ (prefixWord ++ tailWord_670839).sum := by decide
  have hdescent : baseEnd_670839 < baseStart_670839 := by decide
  rcases family_descends (prefixWord ++ tailWord_670839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670884 : List Nat := [2, 3, 1, 2, 3, 3, 8]
def baseStart_670884 : Nat := 118140960795 + 670884 * 2 ^ 59
def prefixEnd_670884 : Nat := 4983230072969 + 3 ^ 40 * 670884 * 2
def baseEnd_670884 : Nat := 8505826059532306097893

theorem tailTrace_670884 : CollatzResearch.WordTrace tailWord_670884 prefixEnd_670884 8505826059532306097893 := by
  unfold tailWord_670884
  simp only [CollatzResearch.WordTrace]
  refine ⟨12234574850754660355149853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16312766467672880473533137 12234574850754660355149853)
  ·
    refine ⟨4587965569032997633181195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12234574850754660355149853 4587965569032997633181195)
    ·
      refine ⟨6881948353549496449771793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4587965569032997633181195 6881948353549496449771793)
      ·
        refine ⟨5161461265162122337328845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6881948353549496449771793 5161461265162122337328845)
        ·
          refine ⟨1935547974435795876498317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5161461265162122337328845 1935547974435795876498317)
          ·
            refine ⟨725830490413423453686869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1935547974435795876498317 725830490413423453686869)
            ·
              refine ⟨8505826059532306097893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 725830490413423453686869 8505826059532306097893)
              ·
                rfl

theorem cell22_670884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 8].length) (baseStart_670884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670884 prefixEnd_670884 := by exact prefixLift 670884
  have htrace : WordTrace (prefixWord ++ tailWord_670884) baseStart_670884 baseEnd_670884 := by
    simpa [prefixWord, tailWord_670884, baseEnd_670884] using wordTrace_append hprefix tailTrace_670884
  have hstable : (prefixWord ++ tailWord_670884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670884).length < 2 ^ (prefixWord ++ tailWord_670884).sum := by decide
  have hdescent : baseEnd_670884 < baseStart_670884 := by decide
  rcases family_descends (prefixWord ++ tailWord_670884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670890 : List Nat := [3, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_670890 : Nat := 118140960795 + 670890 * 2 ^ 59
def prefixEnd_670890 : Nat := 4983230072969 + 3 ^ 40 * 670890 * 2
def baseEnd_670890 : Nat := 76553119176663416331031

theorem tailTrace_670890 : CollatzResearch.WordTrace tailWord_670890 prefixEnd_670890 76553119176663416331031 := by
  unfold tailWord_670890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117342134871895933754531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16312912359658389156678749 6117342134871895933754531)
  ·
    refine ⟨9176013202307843900631797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6117342134871895933754531 9176013202307843900631797)
    ·
      refine ⟨860251237716360365684231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9176013202307843900631797 860251237716360365684231)
      ·
        refine ⟨1290376856574540548526347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860251237716360365684231 1290376856574540548526347)
        ·
          refine ⟨1935565284861810822789521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290376856574540548526347 1935565284861810822789521)
          ·
            refine ⟨1451673963646358117092141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935565284861810822789521 1451673963646358117092141)
            ·
              refine ⟨544377736367384293909553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451673963646358117092141 544377736367384293909553)
              ·
                refine ⟨408283302275538220432165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544377736367384293909553 408283302275538220432165)
                ·
                  refine ⟨76553119176663416331031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408283302275538220432165 76553119176663416331031)
                  ·
                    rfl

theorem cell22_670890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_670890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670890 prefixEnd_670890 := by exact prefixLift 670890
  have htrace : WordTrace (prefixWord ++ tailWord_670890) baseStart_670890 baseEnd_670890 := by
    simpa [prefixWord, tailWord_670890, baseEnd_670890] using wordTrace_append hprefix tailTrace_670890
  have hstable : (prefixWord ++ tailWord_670890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670890).length < 2 ^ (prefixWord ++ tailWord_670890).sum := by decide
  have hdescent : baseEnd_670890 < baseStart_670890 := by decide
  rcases family_descends (prefixWord ++ tailWord_670890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_670927 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 3, 7]
def baseStart_670927 : Nat := 118140960795 + 670927 * 2 ^ 59
def prefixEnd_670927 : Nat := 4983230072969 + 3 ^ 40 * 670927 * 2
def baseEnd_670927 : Nat := 229672023386134485817979

theorem tailTrace_670927 : CollatzResearch.WordTrace tailWord_670927 prefixEnd_670927 229672023386134485817979 := by
  unfold tailWord_670927
  simp only [CollatzResearch.WordTrace]
  refine ⟨24470718040353539054115035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16313812026902359369410023 24470718040353539054115035)
  ·
    refine ⟨36706077060530308581172553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24470718040353539054115035 36706077060530308581172553)
    ·
      refine ⟨27529557795397731435879415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36706077060530308581172553 27529557795397731435879415)
      ·
        refine ⟨41294336693096597153819123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27529557795397731435879415 41294336693096597153819123)
        ·
          refine ⟨61941505039644895730728685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41294336693096597153819123 61941505039644895730728685)
          ·
            refine ⟨23228064389866835899023257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61941505039644895730728685 23228064389866835899023257)
            ·
              refine ⟨17421048292400126924267443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23228064389866835899023257 17421048292400126924267443)
              ·
                refine ⟨26131572438600190386401165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17421048292400126924267443 26131572438600190386401165)
                ·
                  refine ⟨9799339664475071394900437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26131572438600190386401165 9799339664475071394900437)
                  ·
                    refine ⟨229672023386134485817979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9799339664475071394900437 229672023386134485817979)
                    ·
                      rfl

theorem cell22_670927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_670927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_670927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_670927 prefixEnd_670927 := by exact prefixLift 670927
  have htrace : WordTrace (prefixWord ++ tailWord_670927) baseStart_670927 baseEnd_670927 := by
    simpa [prefixWord, tailWord_670927, baseEnd_670927] using wordTrace_append hprefix tailTrace_670927
  have hstable : (prefixWord ++ tailWord_670927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_670927).length < 2 ^ (prefixWord ++ tailWord_670927).sum := by decide
  have hdescent : baseEnd_670927 < baseStart_670927 := by decide
  rcases family_descends (prefixWord ++ tailWord_670927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671034 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_671034 : Nat := 118140960795 + 671034 * 2 ^ 59
def prefixEnd_671034 : Nat := 4983230072969 + 3 ^ 40 * 671034 * 2
def baseEnd_671034 : Nat := 229708651672821873392651

theorem tailTrace_671034 : CollatzResearch.WordTrace tailWord_671034 prefixEnd_671034 229708651672821873392651 := by
  unfold tailWord_671034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118655162741474082065039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16316413767310597552173437 6118655162741474082065039)
  ·
    refine ⟨9177982744112211123097559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6118655162741474082065039 9177982744112211123097559)
    ·
      refine ⟨13766974116168316684646339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9177982744112211123097559 13766974116168316684646339)
      ·
        refine ⟨20650461174252475026969509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13766974116168316684646339 20650461174252475026969509)
        ·
          refine ⟨3871961470172339067556783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20650461174252475026969509 3871961470172339067556783)
          ·
            refine ⟨5807942205258508601335175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871961470172339067556783 5807942205258508601335175)
            ·
              refine ⟨8711913307887762902002763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807942205258508601335175 8711913307887762902002763)
              ·
                refine ⟨13067869961831644353004145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8711913307887762902002763 13067869961831644353004145)
                ·
                  refine ⟨9800902471373733264753109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13067869961831644353004145 9800902471373733264753109)
                  ·
                    refine ⟨229708651672821873392651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9800902471373733264753109 229708651672821873392651)
                    ·
                      rfl

theorem cell22_671034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_671034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671034 prefixEnd_671034 := by exact prefixLift 671034
  have htrace : WordTrace (prefixWord ++ tailWord_671034) baseStart_671034 baseEnd_671034 := by
    simpa [prefixWord, tailWord_671034, baseEnd_671034] using wordTrace_append hprefix tailTrace_671034
  have hstable : (prefixWord ++ tailWord_671034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671034).length < 2 ^ (prefixWord ++ tailWord_671034).sum := by decide
  have hdescent : baseEnd_671034 < baseStart_671034 := by decide
  rcases family_descends (prefixWord ++ tailWord_671034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671036 : List Nat := [2, 2, 2, 2, 1, 3, 4, 6]
def baseStart_671036 : Nat := 118140960795 + 671036 * 2 ^ 59
def prefixEnd_671036 : Nat := 4983230072969 + 3 ^ 40 * 671036 * 2
def baseEnd_671036 : Nat := 25523259590410503871405

theorem tailTrace_671036 : CollatzResearch.WordTrace tailWord_671036 prefixEnd_671036 25523259590410503871405 := by
  unfold tailWord_671036
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237346798479325334916481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16316462397972433779888641 12237346798479325334916481)
  ·
    refine ⟨9178010098859494001187361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12237346798479325334916481 9178010098859494001187361)
    ·
      refine ⟨6883507574144620500890521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9178010098859494001187361 6883507574144620500890521)
      ·
        refine ⟨5162630680608465375667891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6883507574144620500890521 5162630680608465375667891)
        ·
          refine ⟨7743946020912698063501837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162630680608465375667891 7743946020912698063501837)
          ·
            refine ⟨2903979757842261773813189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7743946020912698063501837 2903979757842261773813189)
            ·
              refine ⟨544496204595424082589973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2903979757842261773813189 544496204595424082589973)
              ·
                refine ⟨25523259590410503871405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 544496204595424082589973 25523259590410503871405)
                ·
                  rfl

theorem cell22_671036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 6].length) (baseStart_671036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671036 prefixEnd_671036 := by exact prefixLift 671036
  have htrace : WordTrace (prefixWord ++ tailWord_671036) baseStart_671036 baseEnd_671036 := by
    simpa [prefixWord, tailWord_671036, baseEnd_671036] using wordTrace_append hprefix tailTrace_671036
  have hstable : (prefixWord ++ tailWord_671036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671036).length < 2 ^ (prefixWord ++ tailWord_671036).sum := by decide
  have hdescent : baseEnd_671036 < baseStart_671036 := by decide
  rcases family_descends (prefixWord ++ tailWord_671036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671064 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 7]
def baseStart_671064 : Nat := 118140960795 + 671064 * 2 ^ 59
def prefixEnd_671064 : Nat := 4983230072969 + 3 ^ 40 * 671064 * 2
def baseEnd_671064 : Nat := 76572973761970598380853

theorem tailTrace_671064 : CollatzResearch.WordTrace tailWord_671064 prefixEnd_671064 76572973761970598380853 := by
  unfold tailWord_671064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237857420428605725926123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16317143227238140967901497 12237857420428605725926123)
  ·
    refine ⟨18356786130642908588889185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12237857420428605725926123 18356786130642908588889185)
    ·
      refine ⟨13767589597982181441666889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18356786130642908588889185 13767589597982181441666889)
      ·
        refine ⟨10325692198486636081250167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13767589597982181441666889 10325692198486636081250167)
        ·
          refine ⟨15488538297729954121875251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10325692198486636081250167 15488538297729954121875251)
          ·
            refine ⟨23232807446594931182812877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15488538297729954121875251 23232807446594931182812877)
            ·
              refine ⟨8712302792473099193554829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23232807446594931182812877 8712302792473099193554829)
              ·
                refine ⟨3267113547177412197583061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8712302792473099193554829 3267113547177412197583061)
                ·
                  refine ⟨76572973761970598380853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3267113547177412197583061 76572973761970598380853)
                  ·
                    rfl

theorem cell22_671064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_671064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671064 prefixEnd_671064 := by exact prefixLift 671064
  have htrace : WordTrace (prefixWord ++ tailWord_671064) baseStart_671064 baseEnd_671064 := by
    simpa [prefixWord, tailWord_671064, baseEnd_671064] using wordTrace_append hprefix tailTrace_671064
  have hstable : (prefixWord ++ tailWord_671064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671064).length < 2 ^ (prefixWord ++ tailWord_671064).sum := by decide
  have hdescent : baseEnd_671064 < baseStart_671064 := by decide
  rcases family_descends (prefixWord ++ tailWord_671064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671205 : List Nat := [1, 3, 1, 5, 1, 3, 2, 6]
def baseStart_671205 : Nat := 118140960795 + 671205 * 2 ^ 59
def prefixEnd_671205 : Nat := 4983230072969 + 3 ^ 40 * 671205 * 2
def baseEnd_671205 : Nat := 25529687607492714151903

theorem tailTrace_671205 : CollatzResearch.WordTrace tailWord_671205 prefixEnd_671205 25529687607492714151903 := by
  unfold tailWord_671205
  simp only [CollatzResearch.WordTrace]
  refine ⟨24480857533346392532735069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16320571688897595021823379 24480857533346392532735069)
  ·
    refine ⟨9180321575004897199775651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24480857533346392532735069 9180321575004897199775651)
    ·
      refine ⟨13770482362507345799663477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9180321575004897199775651 13770482362507345799663477)
      ·
        refine ⟨1290982721485063668718451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13770482362507345799663477 1290982721485063668718451)
        ·
          refine ⟨1936474082227595503077677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290982721485063668718451 1936474082227595503077677)
          ·
            refine ⟨726177780835348313654129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1936474082227595503077677 726177780835348313654129)
            ·
              refine ⟨544633335626511235240597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726177780835348313654129 544633335626511235240597)
              ·
                refine ⟨25529687607492714151903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 544633335626511235240597 25529687607492714151903)
                ·
                  rfl

theorem cell22_671205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 6].length) (baseStart_671205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671205 prefixEnd_671205 := by exact prefixLift 671205
  have htrace : WordTrace (prefixWord ++ tailWord_671205) baseStart_671205 baseEnd_671205 := by
    simpa [prefixWord, tailWord_671205, baseEnd_671205] using wordTrace_append hprefix tailTrace_671205
  have hstable : (prefixWord ++ tailWord_671205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671205).length < 2 ^ (prefixWord ++ tailWord_671205).sum := by decide
  have hdescent : baseEnd_671205 < baseStart_671205 := by decide
  rcases family_descends (prefixWord ++ tailWord_671205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671216 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 7]
def baseStart_671216 : Nat := 118140960795 + 671216 * 2 ^ 59
def prefixEnd_671216 : Nat := 4983230072969 + 3 ^ 40 * 671216 * 2
def baseEnd_671216 : Nat := 76590317997411355114031

theorem tailTrace_671216 : CollatzResearch.WordTrace tailWord_671216 prefixEnd_671216 76590317997411355114031 := by
  unfold tailWord_671216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240629368153270705692751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16320839157537694274257001 12240629368153270705692751)
  ·
    refine ⟨18360944052229906058539127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12240629368153270705692751 18360944052229906058539127)
    ·
      refine ⟨27541416078344859087808691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18360944052229906058539127 27541416078344859087808691)
      ·
        refine ⟨41312124117517288631713037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27541416078344859087808691 41312124117517288631713037)
        ·
          refine ⟨15492046544068983236892389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41312124117517288631713037 15492046544068983236892389)
          ·
            refine ⟨2904758727012934356917323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15492046544068983236892389 2904758727012934356917323)
            ·
              refine ⟨4357138090519401535375985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904758727012934356917323 4357138090519401535375985)
              ·
                refine ⟨3267853567889551151531989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357138090519401535375985 3267853567889551151531989)
                ·
                  refine ⟨76590317997411355114031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3267853567889551151531989 76590317997411355114031)
                  ·
                    rfl

theorem cell22_671216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_671216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671216 prefixEnd_671216 := by exact prefixLift 671216
  have htrace : WordTrace (prefixWord ++ tailWord_671216) baseStart_671216 baseEnd_671216 := by
    simpa [prefixWord, tailWord_671216, baseEnd_671216] using wordTrace_append hprefix tailTrace_671216
  have hstable : (prefixWord ++ tailWord_671216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671216).length < 2 ^ (prefixWord ++ tailWord_671216).sum := by decide
  have hdescent : baseEnd_671216 < baseStart_671216 := by decide
  rcases family_descends (prefixWord ++ tailWord_671216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671231 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 2, 5]
def baseStart_671231 : Nat := 118140960795 + 671231 * 2 ^ 59
def prefixEnd_671231 : Nat := 4983230072969 + 3 ^ 40 * 671231 * 2
def baseEnd_671231 : Nat := 229776088798779026217047

theorem tailTrace_671231 : CollatzResearch.WordTrace tailWord_671231 prefixEnd_671231 229776088798779026217047 := by
  unfold tailWord_671231
  simp only [CollatzResearch.WordTrace]
  refine ⟨24481805831252198973181547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16321203887501465982121031 24481805831252198973181547)
  ·
    refine ⟨36722708746878298459772321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24481805831252198973181547 36722708746878298459772321)
    ·
      refine ⟨27542031560158723844829241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36722708746878298459772321 27542031560158723844829241)
      ·
        refine ⟨20656523670119042883621931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27542031560158723844829241 20656523670119042883621931)
        ·
          refine ⟨30984785505178564325432897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20656523670119042883621931 30984785505178564325432897)
          ·
            refine ⟨23238589128883923244074673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30984785505178564325432897 23238589128883923244074673)
            ·
              refine ⟨17428941846662942433056005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23238589128883923244074673 17428941846662942433056005)
              ·
                refine ⟨3267926596249301706198001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17428941846662942433056005 3267926596249301706198001)
                ·
                  refine ⟨2450944947186976279648501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3267926596249301706198001 2450944947186976279648501)
                  ·
                    refine ⟨229776088798779026217047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2450944947186976279648501 229776088798779026217047)
                    ·
                      rfl

theorem cell22_671231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_671231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671231 prefixEnd_671231 := by exact prefixLift 671231
  have htrace : WordTrace (prefixWord ++ tailWord_671231) baseStart_671231 baseEnd_671231 := by
    simpa [prefixWord, tailWord_671231, baseEnd_671231] using wordTrace_append hprefix tailTrace_671231
  have hstable : (prefixWord ++ tailWord_671231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671231).length < 2 ^ (prefixWord ++ tailWord_671231).sum := by decide
  have hdescent : baseEnd_671231 < baseStart_671231 := by decide
  rcases family_descends (prefixWord ++ tailWord_671231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671295 : List Nat := [1, 1, 2, 2, 3, 4, 1, 4, 4]
def baseStart_671295 : Nat := 118140960795 + 671295 * 2 ^ 59
def prefixEnd_671295 : Nat := 4983230072969 + 3 ^ 40 * 671295 * 2
def baseEnd_671295 : Nat := 76599332435568064205617

theorem tailTrace_671295 : CollatzResearch.WordTrace tailWord_671295 prefixEnd_671295 76599332435568064205617 := by
  unfold tailWord_671295
  simp only [CollatzResearch.WordTrace]
  refine ⟨24484140103020337903511339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16322760068680225269007559 24484140103020337903511339)
  ·
    refine ⟨36726210154530506855267009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24484140103020337903511339 36726210154530506855267009)
    ·
      refine ⟨27544657615897880141450257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36726210154530506855267009 27544657615897880141450257)
      ·
        refine ⟨20658493211923410106087693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27544657615897880141450257 20658493211923410106087693)
        ·
          refine ⟨7746934954471278789782885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20658493211923410106087693 7746934954471278789782885)
          ·
            refine ⟨1452550303963364773084291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7746934954471278789782885 1452550303963364773084291)
            ·
              refine ⟨2178825455945047159626437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452550303963364773084291 2178825455945047159626437)
              ·
                refine ⟨408529772989696342429957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2178825455945047159626437 408529772989696342429957)
                ·
                  refine ⟨76599332435568064205617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408529772989696342429957 76599332435568064205617)
                  ·
                    rfl

theorem cell22_671295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 4].length) (baseStart_671295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671295 prefixEnd_671295 := by exact prefixLift 671295
  have htrace : WordTrace (prefixWord ++ tailWord_671295) baseStart_671295 baseEnd_671295 := by
    simpa [prefixWord, tailWord_671295, baseEnd_671295] using wordTrace_append hprefix tailTrace_671295
  have hstable : (prefixWord ++ tailWord_671295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671295).length < 2 ^ (prefixWord ++ tailWord_671295).sum := by decide
  have hdescent : baseEnd_671295 < baseStart_671295 := by decide
  rcases family_descends (prefixWord ++ tailWord_671295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671355 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 3, 3]
def baseStart_671355 : Nat := 118140960795 + 671355 * 2 ^ 59
def prefixEnd_671355 : Nat := 4983230072969 + 3 ^ 40 * 671355 * 2
def baseEnd_671355 : Nat := 229818536532884036116667

theorem tailTrace_671355 : CollatzResearch.WordTrace tailWord_671355 prefixEnd_671355 229818536532884036116667 := by
  unfold tailWord_671355
  simp only [CollatzResearch.WordTrace]
  refine ⟨24486328482802968150695519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16324218988535312100463679 24486328482802968150695519)
  ·
    refine ⟨36729492724204452226043279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24486328482802968150695519 36729492724204452226043279)
    ·
      refine ⟨55094239086306678339064919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36729492724204452226043279 55094239086306678339064919)
      ·
        refine ⟨82641358629460017508597379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55094239086306678339064919 82641358629460017508597379)
        ·
          refine ⟨123962037944190026262896069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82641358629460017508597379 123962037944190026262896069)
          ·
            refine ⟨23242882114535629924293013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123962037944190026262896069 23242882114535629924293013)
            ·
              refine ⟨1089510099118857652701235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23242882114535629924293013 1089510099118857652701235)
              ·
                refine ⟨1634265148678286479051853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089510099118857652701235 1634265148678286479051853)
                ·
                  refine ⟨612849430754357429644445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1634265148678286479051853 612849430754357429644445)
                  ·
                    refine ⟨229818536532884036116667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 612849430754357429644445 229818536532884036116667)
                    ·
                      rfl

theorem cell22_671355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 3].length) (baseStart_671355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671355 prefixEnd_671355 := by exact prefixLift 671355
  have htrace : WordTrace (prefixWord ++ tailWord_671355) baseStart_671355 baseEnd_671355 := by
    simpa [prefixWord, tailWord_671355, baseEnd_671355] using wordTrace_append hprefix tailTrace_671355
  have hstable : (prefixWord ++ tailWord_671355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671355).length < 2 ^ (prefixWord ++ tailWord_671355).sum := by decide
  have hdescent : baseEnd_671355 < baseStart_671355 := by decide
  rcases family_descends (prefixWord ++ tailWord_671355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671406 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_671406 : Nat := 118140960795 + 671406 * 2 ^ 59
def prefixEnd_671406 : Nat := 4983230072969 + 3 ^ 40 * 671406 * 2
def baseEnd_671406 : Nat := 229835994875136903091511

theorem tailTrace_671406 : CollatzResearch.WordTrace tailWord_671406 prefixEnd_671406 229835994875136903091511 := by
  unfold tailWord_671406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3061023575702275482600259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16325459070412135907201381 3061023575702275482600259)
  ·
    refine ⟨4591535363553413223900389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3061023575702275482600259 4591535363553413223900389)
    ·
      refine ⟨860912880666264979481323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4591535363553413223900389 860912880666264979481323)
      ·
        refine ⟨1291369320999397469221985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860912880666264979481323 1291369320999397469221985)
        ·
          refine ⟨968526990749548101916489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1291369320999397469221985 968526990749548101916489)
          ·
            refine ⟨726395243062161076437367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 968526990749548101916489 726395243062161076437367)
            ·
              refine ⟨1089592864593241614656051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726395243062161076437367 1089592864593241614656051)
              ·
                refine ⟨1634389296889862421984077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089592864593241614656051 1634389296889862421984077)
                ·
                  refine ⟨612895986333698408244029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1634389296889862421984077 612895986333698408244029)
                  ·
                    refine ⟨229835994875136903091511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 612895986333698408244029 229835994875136903091511)
                    ·
                      rfl

theorem cell22_671406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_671406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671406 prefixEnd_671406 := by exact prefixLift 671406
  have htrace : WordTrace (prefixWord ++ tailWord_671406) baseStart_671406 baseEnd_671406 := by
    simpa [prefixWord, tailWord_671406, baseEnd_671406] using wordTrace_append hprefix tailTrace_671406
  have hstable : (prefixWord ++ tailWord_671406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671406).length < 2 ^ (prefixWord ++ tailWord_671406).sum := by decide
  have hdescent : baseEnd_671406 < baseStart_671406 := by decide
  rcases family_descends (prefixWord ++ tailWord_671406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671458 : List Nat := [3, 3, 16]
def baseStart_671458 : Nat := 118140960795 + 671458 * 2 ^ 59
def prefixEnd_671458 : Nat := 4983230072969 + 3 ^ 40 * 671458 * 2
def baseEnd_671458 : Nat := 105100043684419799173

theorem tailTrace_671458 : CollatzResearch.WordTrace tailWord_671458 prefixEnd_671458 105100043684419799173 := by
  unfold tailWord_671458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122521300357454185423757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16326723467619877827796685 6122521300357454185423757)
  ·
    refine ⟨2295945487634045319533909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6122521300357454185423757 2295945487634045319533909)
    ·
      refine ⟨105100043684419799173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 2295945487634045319533909 105100043684419799173)
      ·
        rfl

theorem cell22_671458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 16].length) (baseStart_671458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671458 prefixEnd_671458 := by exact prefixLift 671458
  have htrace : WordTrace (prefixWord ++ tailWord_671458) baseStart_671458 baseEnd_671458 := by
    simpa [prefixWord, tailWord_671458, baseEnd_671458] using wordTrace_append hprefix tailTrace_671458
  have hstable : (prefixWord ++ tailWord_671458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671458).length < 2 ^ (prefixWord ++ tailWord_671458).sum := by decide
  have hdescent : baseEnd_671458 < baseStart_671458 := by decide
  rcases family_descends (prefixWord ++ tailWord_671458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671460 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_671460 : Nat := 118140960795 + 671460 * 2 ^ 59
def prefixEnd_671460 : Nat := 4983230072969 + 3 ^ 40 * 671460 * 2
def baseEnd_671460 : Nat := 229854480178698762241345

theorem tailTrace_671460 : CollatzResearch.WordTrace tailWord_671460 prefixEnd_671460 229854480178698762241345 := by
  unfold tailWord_671460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245079073711285541633917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16326772098281714055511889 12245079073711285541633917)
  ·
    refine ⟨4591904652641732078112719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12245079073711285541633917 4591904652641732078112719)
    ·
      refine ⟨6887856978962598117169079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4591904652641732078112719 6887856978962598117169079)
      ·
        refine ⟨10331785468443897175753619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6887856978962598117169079 10331785468443897175753619)
        ·
          refine ⟨15497678202665845763630429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10331785468443897175753619 15497678202665845763630429)
          ·
            refine ⟨5811629325999692161361411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15497678202665845763630429 5811629325999692161361411)
            ·
              refine ⟨8717443988999538242042117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811629325999692161361411 8717443988999538242042117)
              ·
                refine ⟨1634520747937413420382897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8717443988999538242042117 1634520747937413420382897)
                ·
                  refine ⟨1225890560953060065287173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1634520747937413420382897 1225890560953060065287173)
                  ·
                    refine ⟨229854480178698762241345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1225890560953060065287173 229854480178698762241345)
                    ·
                      rfl

theorem cell22_671460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_671460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671460 prefixEnd_671460 := by exact prefixLift 671460
  have htrace : WordTrace (prefixWord ++ tailWord_671460) baseStart_671460 baseEnd_671460 := by
    simpa [prefixWord, tailWord_671460, baseEnd_671460] using wordTrace_append hprefix tailTrace_671460
  have hstable : (prefixWord ++ tailWord_671460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671460).length < 2 ^ (prefixWord ++ tailWord_671460).sum := by decide
  have hdescent : baseEnd_671460 < baseStart_671460 := by decide
  rcases family_descends (prefixWord ++ tailWord_671460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671464 : List Nat := [2, 1, 4, 1, 3, 1, 4, 2, 4]
def baseStart_671464 : Nat := 118140960795 + 671464 * 2 ^ 59
def prefixEnd_671464 : Nat := 4983230072969 + 3 ^ 40 * 671464 * 2
def baseEnd_671464 : Nat := 76618616486814695047111

theorem tailTrace_671464 : CollatzResearch.WordTrace tailWord_671464 prefixEnd_671464 76618616486814695047111 := by
  unfold tailWord_671464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245152019704039883206723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16326869359605386510942297 12245152019704039883206723)
  ·
    refine ⟨18367728029556059824810085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12245152019704039883206723 18367728029556059824810085)
    ·
      refine ⟨3443949005541761217151891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18367728029556059824810085 3443949005541761217151891)
      ·
        refine ⟨5165923508312641825727837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443949005541761217151891 5165923508312641825727837)
        ·
          refine ⟨1937221315617240684647939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5165923508312641825727837 1937221315617240684647939)
          ·
            refine ⟨2905831973425861026971909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937221315617240684647939 2905831973425861026971909)
            ·
              refine ⟨544843495017348942557233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2905831973425861026971909 544843495017348942557233)
              ·
                refine ⟨408632621263011706917925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 544843495017348942557233 408632621263011706917925)
                ·
                  refine ⟨76618616486814695047111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408632621263011706917925 76618616486814695047111)
                  ·
                    rfl

theorem cell22_671464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 4].length) (baseStart_671464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671464 prefixEnd_671464 := by exact prefixLift 671464
  have htrace : WordTrace (prefixWord ++ tailWord_671464) baseStart_671464 baseEnd_671464 := by
    simpa [prefixWord, tailWord_671464, baseEnd_671464] using wordTrace_append hprefix tailTrace_671464
  have hstable : (prefixWord ++ tailWord_671464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671464).length < 2 ^ (prefixWord ++ tailWord_671464).sum := by decide
  have hdescent : baseEnd_671464 < baseStart_671464 := by decide
  rcases family_descends (prefixWord ++ tailWord_671464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671492 : List Nat := [2, 3, 2, 2, 1, 3, 3, 6]
def baseStart_671492 : Nat := 118140960795 + 671492 * 2 ^ 59
def prefixEnd_671492 : Nat := 4983230072969 + 3 ^ 40 * 671492 * 2
def baseEnd_671492 : Nat := 25540603825851260604583

theorem tailTrace_671492 : CollatzResearch.WordTrace tailWord_671492 prefixEnd_671492 25540603825851260604583 := by
  unfold tailWord_671492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245662641653320274216365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16327550188871093698955153 12245662641653320274216365)
  ·
    refine ⟨4592123490619995102831137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12245662641653320274216365 4592123490619995102831137)
    ·
      refine ⟨3444092617964996327123353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4592123490619995102831137 3444092617964996327123353)
      ·
        refine ⟨2583069463473747245342515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3444092617964996327123353 2583069463473747245342515)
        ·
          refine ⟨3874604195210620868013773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583069463473747245342515 3874604195210620868013773)
          ·
            refine ⟨1452976573203982825505165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3874604195210620868013773 1452976573203982825505165)
            ·
              refine ⟨544866214951493559564437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1452976573203982825505165 544866214951493559564437)
              ·
                refine ⟨25540603825851260604583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 544866214951493559564437 25540603825851260604583)
                ·
                  rfl

theorem cell22_671492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 6].length) (baseStart_671492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671492 prefixEnd_671492 := by exact prefixLift 671492
  have htrace : WordTrace (prefixWord ++ tailWord_671492) baseStart_671492 baseEnd_671492 := by
    simpa [prefixWord, tailWord_671492, baseEnd_671492] using wordTrace_append hprefix tailTrace_671492
  have hstable : (prefixWord ++ tailWord_671492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671492).length < 2 ^ (prefixWord ++ tailWord_671492).sum := by decide
  have hdescent : baseEnd_671492 < baseStart_671492 := by decide
  rcases family_descends (prefixWord ++ tailWord_671492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671520 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 7]
def baseStart_671520 : Nat := 118140960795 + 671520 * 2 ^ 59
def prefixEnd_671520 : Nat := 4983230072969 + 3 ^ 40 * 671520 * 2
def baseEnd_671520 : Nat := 76625006468292868580387

theorem tailTrace_671520 : CollatzResearch.WordTrace tailWord_671520 prefixEnd_671520 76625006468292868580387 := by
  unfold tailWord_671520
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246173263602600665226007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16328231018136800886968009 12246173263602600665226007)
  ·
    refine ⟨18369259895403900997839011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12246173263602600665226007 18369259895403900997839011)
    ·
      refine ⟨27553889843105851496758517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18369259895403900997839011 27553889843105851496758517)
      ·
        refine ⟨2583177172791173577821111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27553889843105851496758517 2583177172791173577821111)
        ·
          refine ⟨3874765759186760366731667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583177172791173577821111 3874765759186760366731667)
          ·
            refine ⟨5812148638780140550097501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874765759186760366731667 5812148638780140550097501)
            ·
              refine ⟨2179555739542552706286563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5812148638780140550097501 2179555739542552706286563)
              ·
                refine ⟨3269333609313829059429845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2179555739542552706286563 3269333609313829059429845)
                ·
                  refine ⟨76625006468292868580387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3269333609313829059429845 76625006468292868580387)
                  ·
                    rfl

theorem cell22_671520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_671520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671520 prefixEnd_671520 := by exact prefixLift 671520
  have htrace : WordTrace (prefixWord ++ tailWord_671520) baseStart_671520 baseEnd_671520 := by
    simpa [prefixWord, tailWord_671520, baseEnd_671520] using wordTrace_append hprefix tailTrace_671520
  have hstable : (prefixWord ++ tailWord_671520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671520).length < 2 ^ (prefixWord ++ tailWord_671520).sum := by decide
  have hdescent : baseEnd_671520 < baseStart_671520 := by decide
  rcases family_descends (prefixWord ++ tailWord_671520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671524 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_671524 : Nat := 118140960795 + 671524 * 2 ^ 59
def prefixEnd_671524 : Nat := 4983230072969 + 3 ^ 40 * 671524 * 2
def baseEnd_671524 : Nat := 229876388686623928641149

theorem tailTrace_671524 : CollatzResearch.WordTrace tailWord_671524 prefixEnd_671524 229876388686623928641149 := by
  unfold tailWord_671524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246246209595355006798813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16328328279460473342398417 12246246209595355006798813)
  ·
    refine ⟨4592342328598258127549555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12246246209595355006798813 4592342328598258127549555)
    ·
      refine ⟨6888513492897387191324333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4592342328598258127549555 6888513492897387191324333)
      ·
        refine ⟨2583192559836520196746625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6888513492897387191324333 2583192559836520196746625)
        ·
          refine ⟨1937394419877390147559969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2583192559836520196746625 1937394419877390147559969)
          ·
            refine ⟨1453045814908042610669977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1937394419877390147559969 1453045814908042610669977)
            ·
              refine ⟨1089784361181031958002483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453045814908042610669977 1089784361181031958002483)
              ·
                refine ⟨1634676541771547937003725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089784361181031958002483 1634676541771547937003725)
                ·
                  refine ⟨613003703164330476376397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1634676541771547937003725 613003703164330476376397)
                  ·
                    refine ⟨229876388686623928641149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613003703164330476376397 229876388686623928641149)
                    ·
                      rfl

theorem cell22_671524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_671524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671524 prefixEnd_671524 := by exact prefixLift 671524
  have htrace : WordTrace (prefixWord ++ tailWord_671524) baseStart_671524 baseEnd_671524 := by
    simpa [prefixWord, tailWord_671524, baseEnd_671524] using wordTrace_append hprefix tailTrace_671524
  have hstable : (prefixWord ++ tailWord_671524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671524).length < 2 ^ (prefixWord ++ tailWord_671524).sum := by decide
  have hdescent : baseEnd_671524 < baseStart_671524 := by decide
  rcases family_descends (prefixWord ++ tailWord_671524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671595 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 6, 4]
def baseStart_671595 : Nat := 118140960795 + 671595 * 2 ^ 59
def prefixEnd_671595 : Nat := 4983230072969 + 3 ^ 40 * 671595 * 2
def baseEnd_671595 : Nat := 229900693437603410115931

theorem tailTrace_671595 : CollatzResearch.WordTrace tailWord_671595 prefixEnd_671595 229900693437603410115931 := by
  unfold tailWord_671595
  simp only [CollatzResearch.WordTrace]
  refine ⟨24495082001933489139432239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16330054667955659426288159 24495082001933489139432239)
  ·
    refine ⟨36742623002900233709148359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24495082001933489139432239 36742623002900233709148359)
    ·
      refine ⟨55113934504350350563722539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36742623002900233709148359 55113934504350350563722539)
      ·
        refine ⟨82670901756525525845583809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55113934504350350563722539 82670901756525525845583809)
        ·
          refine ⟨62003176317394144384187857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82670901756525525845583809 62003176317394144384187857)
          ·
            refine ⟨46502382238045608288140893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62003176317394144384187857 46502382238045608288140893)
            ·
              refine ⟨17438393339267103108052835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46502382238045608288140893 17438393339267103108052835)
              ·
                refine ⟨26157590008900654662079253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17438393339267103108052835 26157590008900654662079253)
                ·
                  refine ⟨1226137031667218187284965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26157590008900654662079253 1226137031667218187284965)
                  ·
                    refine ⟨229900693437603410115931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1226137031667218187284965 229900693437603410115931)
                    ·
                      rfl

theorem cell22_671595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 4].length) (baseStart_671595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671595 prefixEnd_671595 := by exact prefixLift 671595
  have htrace : WordTrace (prefixWord ++ tailWord_671595) baseStart_671595 baseEnd_671595 := by
    simpa [prefixWord, tailWord_671595, baseEnd_671595] using wordTrace_append hprefix tailTrace_671595
  have hstable : (prefixWord ++ tailWord_671595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671595).length < 2 ^ (prefixWord ++ tailWord_671595).sum := by decide
  have hdescent : baseEnd_671595 < baseStart_671595 := by decide
  rcases family_descends (prefixWord ++ tailWord_671595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671610 : List Nat := [3, 1, 1, 1, 1, 1, 6, 8]
def baseStart_671610 : Nat := 118140960795 + 671610 * 2 ^ 59
def prefixEnd_671610 : Nat := 4983230072969 + 3 ^ 40 * 671610 * 2
def baseEnd_671610 : Nat := 25545092027127596776765

theorem tailTrace_671610 : CollatzResearch.WordTrace tailWord_671610 prefixEnd_671610 25545092027127596776765 := by
  unfold tailWord_671610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123907274219786675307071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16330419397919431134152189 6123907274219786675307071)
  ·
    refine ⟨9185860911329680012960607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6123907274219786675307071 9185860911329680012960607)
    ·
      refine ⟨13778791366994520019440911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9185860911329680012960607 13778791366994520019440911)
      ·
        refine ⟨20668187050491780029161367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13778791366994520019440911 20668187050491780029161367)
        ·
          refine ⟨31002280575737670043742051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20668187050491780029161367 31002280575737670043742051)
          ·
            refine ⟨46503420863606505065613077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31002280575737670043742051 46503420863606505065613077)
            ·
              refine ⟨2179847852981554924950613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46503420863606505065613077 2179847852981554924950613)
              ·
                refine ⟨25545092027127596776765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2179847852981554924950613 25545092027127596776765)
                ·
                  rfl

theorem cell22_671610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_671610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671610 prefixEnd_671610 := by exact prefixLift 671610
  have htrace : WordTrace (prefixWord ++ tailWord_671610) baseStart_671610 baseEnd_671610 := by
    simpa [prefixWord, tailWord_671610, baseEnd_671610] using wordTrace_append hprefix tailTrace_671610
  have hstable : (prefixWord ++ tailWord_671610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671610).length < 2 ^ (prefixWord ++ tailWord_671610).sum := by decide
  have hdescent : baseEnd_671610 < baseStart_671610 := by decide
  rcases family_descends (prefixWord ++ tailWord_671610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671614 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_671614 : Nat := 118140960795 + 671614 * 2 ^ 59
def prefixEnd_671614 : Nat := 4983230072969 + 3 ^ 40 * 671614 * 2
def baseEnd_671614 : Nat := 229907197525893693890873

theorem tailTrace_671614 : CollatzResearch.WordTrace tailWord_671614 prefixEnd_671614 229907197525893693890873 := by
  unfold tailWord_671614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3061971873608081923046737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16330516659243103589582597 3061971873608081923046737)
  ·
    refine ⟨2296478905206061442285053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3061971873608081923046737 2296478905206061442285053)
    ·
      refine ⟨861179589452273040856895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2296478905206061442285053 861179589452273040856895)
      ·
        refine ⟨1291769384178409561285343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 861179589452273040856895 1291769384178409561285343)
        ·
          refine ⟨1937654076267614341928015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291769384178409561285343 1937654076267614341928015)
          ·
            refine ⟨2906481114401421512892023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937654076267614341928015 2906481114401421512892023)
            ·
              refine ⟨4359721671602132269338035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906481114401421512892023 4359721671602132269338035)
              ·
                refine ⟨6539582507403198404007053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359721671602132269338035 6539582507403198404007053)
                ·
                  refine ⟨2452343440276199401502645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6539582507403198404007053 2452343440276199401502645)
                  ·
                    refine ⟨229907197525893693890873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2452343440276199401502645 229907197525893693890873)
                    ·
                      rfl

theorem cell22_671614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_671614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671614 prefixEnd_671614 := by exact prefixLift 671614
  have htrace : WordTrace (prefixWord ++ tailWord_671614) baseStart_671614 baseEnd_671614 := by
    simpa [prefixWord, tailWord_671614, baseEnd_671614] using wordTrace_append hprefix tailTrace_671614
  have hstable : (prefixWord ++ tailWord_671614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671614).length < 2 ^ (prefixWord ++ tailWord_671614).sum := by decide
  have hdescent : baseEnd_671614 < baseStart_671614 := by decide
  rcases family_descends (prefixWord ++ tailWord_671614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671644 : List Nat := [2, 2, 3, 3, 1, 3, 1, 7]
def baseStart_671644 : Nat := 118140960795 + 671644 * 2 ^ 59
def prefixEnd_671644 : Nat := 4983230072969 + 3 ^ 40 * 671644 * 2
def baseEnd_671644 : Nat := 25546385237664846182309

theorem tailTrace_671644 : CollatzResearch.WordTrace tailWord_671644 prefixEnd_671644 25546385237664846182309 := by
  unfold tailWord_671644
  simp only [CollatzResearch.WordTrace]
  refine ⟨12248434589377985253982993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16331246119170647005310657 12248434589377985253982993)
  ·
    refine ⟨9186325942033488940487245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12248434589377985253982993 9186325942033488940487245)
    ·
      refine ⟨3444872228262558352682717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9186325942033488940487245 3444872228262558352682717)
      ·
        refine ⟨1291827085598459382256019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3444872228262558352682717 1291827085598459382256019)
        ·
          refine ⟨1937740628397689073384029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291827085598459382256019 1937740628397689073384029)
          ·
            refine ⟨726652735649133402519011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1937740628397689073384029 726652735649133402519011)
            ·
              refine ⟨1089979103473700103778517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726652735649133402519011 1089979103473700103778517)
              ·
                refine ⟨25546385237664846182309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1089979103473700103778517 25546385237664846182309)
                ·
                  rfl

theorem cell22_671644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 7].length) (baseStart_671644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671644 prefixEnd_671644 := by exact prefixLift 671644
  have htrace : WordTrace (prefixWord ++ tailWord_671644) baseStart_671644 baseEnd_671644 := by
    simpa [prefixWord, tailWord_671644, baseEnd_671644] using wordTrace_append hprefix tailTrace_671644
  have hstable : (prefixWord ++ tailWord_671644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671644).length < 2 ^ (prefixWord ++ tailWord_671644).sum := by decide
  have hdescent : baseEnd_671644 < baseStart_671644 := by decide
  rcases family_descends (prefixWord ++ tailWord_671644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671706 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_671706 : Nat := 118140960795 + 671706 * 2 ^ 59
def prefixEnd_671706 : Nat := 4983230072969 + 3 ^ 40 * 671706 * 2
def baseEnd_671706 : Nat := 76646230335345373530197

theorem tailTrace_671706 : CollatzResearch.WordTrace tailWord_671706 prefixEnd_671706 76646230335345373530197 := by
  unfold tailWord_671706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124782626132838774180743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16332753669687570064481981 6124782626132838774180743)
  ·
    refine ⟨9187173939199258161271115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6124782626132838774180743 9187173939199258161271115)
    ·
      refine ⟨13780760908798887241906673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9187173939199258161271115 13780760908798887241906673)
      ·
        refine ⟨10335570681599165431430005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13780760908798887241906673 10335570681599165431430005)
        ·
          refine ⟨968959751399921759196563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10335570681599165431430005 968959751399921759196563)
          ·
            refine ⟨1453439627099882638794845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968959751399921759196563 1453439627099882638794845)
            ·
              refine ⟨545039860162455989548067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1453439627099882638794845 545039860162455989548067)
              ·
                refine ⟨817559790243683984322101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545039860162455989548067 817559790243683984322101)
                ·
                  refine ⟨76646230335345373530197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 817559790243683984322101 76646230335345373530197)
                  ·
                    rfl

theorem cell22_671706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_671706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671706 prefixEnd_671706 := by exact prefixLift 671706
  have htrace : WordTrace (prefixWord ++ tailWord_671706) baseStart_671706 baseEnd_671706 := by
    simpa [prefixWord, tailWord_671706, baseEnd_671706] using wordTrace_append hprefix tailTrace_671706
  have hstable : (prefixWord ++ tailWord_671706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671706).length < 2 ^ (prefixWord ++ tailWord_671706).sum := by decide
  have hdescent : baseEnd_671706 < baseStart_671706 := by decide
  rcases family_descends (prefixWord ++ tailWord_671706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671749 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_671749 : Nat := 118140960795 + 671749 * 2 ^ 59
def prefixEnd_671749 : Nat := 4983230072969 + 3 ^ 40 * 671749 * 2
def baseEnd_671749 : Nat := 229953410784798341765459

theorem tailTrace_671749 : CollatzResearch.WordTrace tailWord_671749 prefixEnd_671749 229953410784798341765459 := by
  unfold tailWord_671749
  simp only [CollatzResearch.WordTrace]
  refine ⟨24500698843375573440538301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16333799228917048960358867 24500698843375573440538301)
  ·
    refine ⟨9187762066265840040201863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24500698843375573440538301 9187762066265840040201863)
    ·
      refine ⟨13781643099398760060302795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9187762066265840040201863 13781643099398760060302795)
      ·
        refine ⟨20672464649098140090454193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13781643099398760060302795 20672464649098140090454193)
        ·
          refine ⟨15504348486823605067840645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20672464649098140090454193 15504348486823605067840645)
          ·
            refine ⟨2907065341279425950220121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15504348486823605067840645 2907065341279425950220121)
            ·
              refine ⟨2180299005959569462665091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2907065341279425950220121 2180299005959569462665091)
              ·
                refine ⟨3270448508939354193997637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2180299005959569462665091 3270448508939354193997637)
                ·
                  refine ⟨613209095426128911374557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3270448508939354193997637 613209095426128911374557)
                  ·
                    refine ⟨229953410784798341765459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613209095426128911374557 229953410784798341765459)
                    ·
                      rfl

theorem cell22_671749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_671749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671749 prefixEnd_671749 := by exact prefixLift 671749
  have htrace : WordTrace (prefixWord ++ tailWord_671749) baseStart_671749 baseEnd_671749 := by
    simpa [prefixWord, tailWord_671749, baseEnd_671749] using wordTrace_append hprefix tailTrace_671749
  have hstable : (prefixWord ++ tailWord_671749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671749).length < 2 ^ (prefixWord ++ tailWord_671749).sum := by decide
  have hdescent : baseEnd_671749 < baseStart_671749 := by decide
  rcases family_descends (prefixWord ++ tailWord_671749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671757 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 5]
def baseStart_671757 : Nat := 118140960795 + 671757 * 2 ^ 59
def prefixEnd_671757 : Nat := 4983230072969 + 3 ^ 40 * 671757 * 2
def baseEnd_671757 : Nat := 76652049782762995855145

theorem tailTrace_671757 : CollatzResearch.WordTrace tailWord_671757 prefixEnd_671757 76652049782762995855145 := by
  unfold tailWord_671757
  simp only [CollatzResearch.WordTrace]
  refine ⟨24500990627346590806829525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16333993751564393871219683 24500990627346590806829525)
  ·
    refine ⟨574241967828435722035067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 24500990627346590806829525 574241967828435722035067)
    ·
      refine ⟨861362951742653583052601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574241967828435722035067 861362951742653583052601)
      ·
        refine ⟨646022213806990187289451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 861362951742653583052601 646022213806990187289451)
        ·
          refine ⟨969033320710485280934177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646022213806990187289451 969033320710485280934177)
          ·
            refine ⟨726774990532863960700633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 969033320710485280934177 726774990532863960700633)
            ·
              refine ⟨545081242899647970525475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726774990532863960700633 545081242899647970525475)
              ·
                refine ⟨817621864349471955788213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545081242899647970525475 817621864349471955788213)
                ·
                  refine ⟨76652049782762995855145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 817621864349471955788213 76652049782762995855145)
                  ·
                    rfl

theorem cell22_671757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_671757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671757 prefixEnd_671757 := by exact prefixLift 671757
  have htrace : WordTrace (prefixWord ++ tailWord_671757) baseStart_671757 baseEnd_671757 := by
    simpa [prefixWord, tailWord_671757, baseEnd_671757] using wordTrace_append hprefix tailTrace_671757
  have hstable : (prefixWord ++ tailWord_671757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671757).length < 2 ^ (prefixWord ++ tailWord_671757).sum := by decide
  have hdescent : baseEnd_671757 < baseStart_671757 := by decide
  rcases family_descends (prefixWord ++ tailWord_671757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671796 : List Nat := [2, 5, 1, 2, 3, 9]
def baseStart_671796 : Nat := 118140960795 + 671796 * 2 ^ 59
def prefixEnd_671796 : Nat := 4983230072969 + 3 ^ 40 * 671796 * 2
def baseEnd_671796 : Nat := 2839129627719825751115

theorem tailTrace_671796 : CollatzResearch.WordTrace tailWord_671796 prefixEnd_671796 2839129627719825751115 := by
  unfold tailWord_671796
  simp only [CollatzResearch.WordTrace]
  refine ⟨12251206537102650233749621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16334942049470200311666161 12251206537102650233749621)
  ·
    refine ⟨1148550612853373459414027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12251206537102650233749621 1148550612853373459414027)
    ·
      refine ⟨1722825919280060189121041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1148550612853373459414027 1722825919280060189121041)
      ·
        refine ⟨1292119439460045141840781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1722825919280060189121041 1292119439460045141840781)
        ·
          refine ⟨484544789797516928190293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1292119439460045141840781 484544789797516928190293)
          ·
            refine ⟨2839129627719825751115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 484544789797516928190293 2839129627719825751115)
            ·
              rfl

theorem cell22_671796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 9].length) (baseStart_671796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671796 prefixEnd_671796 := by exact prefixLift 671796
  have htrace : WordTrace (prefixWord ++ tailWord_671796) baseStart_671796 baseEnd_671796 := by
    simpa [prefixWord, tailWord_671796, baseEnd_671796] using wordTrace_append hprefix tailTrace_671796
  have hstable : (prefixWord ++ tailWord_671796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671796).length < 2 ^ (prefixWord ++ tailWord_671796).sum := by decide
  have hdescent : baseEnd_671796 < baseStart_671796 := by decide
  rcases family_descends (prefixWord ++ tailWord_671796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671807 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 7]
def baseStart_671807 : Nat := 118140960795 + 671807 * 2 ^ 59
def prefixEnd_671807 : Nat := 4983230072969 + 3 ^ 40 * 671807 * 2
def baseEnd_671807 : Nat := 76657755123368507938427

theorem tailTrace_671807 : CollatzResearch.WordTrace tailWord_671807 prefixEnd_671807 76657755123368507938427 := by
  unfold tailWord_671807
  simp only [CollatzResearch.WordTrace]
  refine ⟨24502814277165449346149675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16335209518110299564099783 24502814277165449346149675)
  ·
    refine ⟨36754221415748174019224513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24502814277165449346149675 36754221415748174019224513)
    ·
      refine ⟨27565666061811130514418385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36754221415748174019224513 27565666061811130514418385)
      ·
        refine ⟨20674249546358347885813789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27565666061811130514418385 20674249546358347885813789)
        ·
          refine ⟨7752843579884380457180171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20674249546358347885813789 7752843579884380457180171)
          ·
            refine ⟨11629265369826570685770257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7752843579884380457180171 11629265369826570685770257)
            ·
              refine ⟨8721949027369928014327693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11629265369826570685770257 8721949027369928014327693)
              ·
                refine ⟨3270730885263723005372885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8721949027369928014327693 3270730885263723005372885)
                ·
                  refine ⟨76657755123368507938427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3270730885263723005372885 76657755123368507938427)
                  ·
                    rfl

theorem cell22_671807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 7].length) (baseStart_671807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671807 prefixEnd_671807 := by exact prefixLift 671807
  have htrace : WordTrace (prefixWord ++ tailWord_671807) baseStart_671807 baseEnd_671807 := by
    simpa [prefixWord, tailWord_671807, baseEnd_671807] using wordTrace_append hprefix tailTrace_671807
  have hstable : (prefixWord ++ tailWord_671807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671807).length < 2 ^ (prefixWord ++ tailWord_671807).sum := by decide
  have hdescent : baseEnd_671807 < baseStart_671807 := by decide
  rcases family_descends (prefixWord ++ tailWord_671807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671809 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_671809 : Nat := 118140960795 + 671809 * 2 ^ 59
def prefixEnd_671809 : Nat := 4983230072969 + 3 ^ 40 * 671809 * 2
def baseEnd_671809 : Nat := 229973950010978185265275

theorem tailTrace_671809 : CollatzResearch.WordTrace tailWord_671809 prefixEnd_671809 229973950010978185265275 := by
  unfold tailWord_671809
  simp only [CollatzResearch.WordTrace]
  refine ⟨24502887223158203687722481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16335258148772135791814987 24502887223158203687722481)
  ·
    refine ⟨18377165417368652765791861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24502887223158203687722481 18377165417368652765791861)
    ·
      refine ⟨1722859257878311196792987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18377165417368652765791861 1722859257878311196792987)
      ·
        refine ⟨2584288886817466795189481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1722859257878311196792987 2584288886817466795189481)
        ·
          refine ⟨1938216665113100096392111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2584288886817466795189481 1938216665113100096392111)
          ·
            refine ⟨2907324997669650144588167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938216665113100096392111 2907324997669650144588167)
            ·
              refine ⟨4360987496504475216882251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907324997669650144588167 4360987496504475216882251)
              ·
                refine ⟨6541481244756712825323377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4360987496504475216882251 6541481244756712825323377)
                ·
                  refine ⟨4906110933567534618992533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6541481244756712825323377 4906110933567534618992533)
                  ·
                    refine ⟨229973950010978185265275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4906110933567534618992533 229973950010978185265275)
                    ·
                      rfl

theorem cell22_671809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_671809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671809 prefixEnd_671809 := by exact prefixLift 671809
  have htrace : WordTrace (prefixWord ++ tailWord_671809) baseStart_671809 baseEnd_671809 := by
    simpa [prefixWord, tailWord_671809, baseEnd_671809] using wordTrace_append hprefix tailTrace_671809
  have hstable : (prefixWord ++ tailWord_671809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671809).length < 2 ^ (prefixWord ++ tailWord_671809).sum := by decide
  have hdescent : baseEnd_671809 < baseStart_671809 := by decide
  rcases family_descends (prefixWord ++ tailWord_671809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671867 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 9]
def baseStart_671867 : Nat := 118140960795 + 671867 * 2 ^ 59
def prefixEnd_671867 : Nat := 4983230072969 + 3 ^ 40 * 671867 * 2
def baseEnd_671867 : Nat := 229993804596285367315097

theorem tailTrace_671867 : CollatzResearch.WordTrace tailWord_671867 prefixEnd_671867 229993804596285367315097 := by
  unfold tailWord_671867
  simp only [CollatzResearch.WordTrace]
  refine ⟨24505002656948079593333855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16336668437965386395555903 24505002656948079593333855)
  ·
    refine ⟨36757503985422119390000783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24505002656948079593333855 36757503985422119390000783)
    ·
      refine ⟨55136255978133179085001175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36757503985422119390000783 55136255978133179085001175)
      ·
        refine ⟨82704383967199768627501763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55136255978133179085001175 82704383967199768627501763)
        ·
          refine ⟨124056575950799652941252645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82704383967199768627501763 124056575950799652941252645)
          ·
            refine ⟨23260607990774934926484871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124056575950799652941252645 23260607990774934926484871)
            ·
              refine ⟨34890911986162402389727307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23260607990774934926484871 34890911986162402389727307)
              ·
                refine ⟨52336367979243603584590961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34890911986162402389727307 52336367979243603584590961)
                ·
                  refine ⟨39252275984432702688443221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52336367979243603584590961 39252275984432702688443221)
                  ·
                    refine ⟨229993804596285367315097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 39252275984432702688443221 229993804596285367315097)
                    ·
                      rfl

theorem cell22_671867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_671867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671867 prefixEnd_671867 := by exact prefixLift 671867
  have htrace : WordTrace (prefixWord ++ tailWord_671867) baseStart_671867 baseEnd_671867 := by
    simpa [prefixWord, tailWord_671867, baseEnd_671867] using wordTrace_append hprefix tailTrace_671867
  have hstable : (prefixWord ++ tailWord_671867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671867).length < 2 ^ (prefixWord ++ tailWord_671867).sum := by decide
  have hdescent : baseEnd_671867 < baseStart_671867 := by decide
  rcases family_descends (prefixWord ++ tailWord_671867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671869 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 6]
def baseStart_671869 : Nat := 118140960795 + 671869 * 2 ^ 59
def prefixEnd_671869 : Nat := 4983230072969 + 3 ^ 40 * 671869 * 2
def baseEnd_671869 : Nat := 76664829745719342921697

theorem tailTrace_671869 : CollatzResearch.WordTrace tailWord_671869 prefixEnd_671869 76664829745719342921697 := by
  unfold tailWord_671869
  simp only [CollatzResearch.WordTrace]
  refine ⟨24505075602940833934906661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16336717068627222623271107 24505075602940833934906661)
  ·
    refine ⟨4594701675551406362794999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24505075602940833934906661 4594701675551406362794999)
    ·
      refine ⟨6892052513327109544192499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4594701675551406362794999 6892052513327109544192499)
      ·
        refine ⟨10338078769990664316288749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892052513327109544192499 10338078769990664316288749)
        ·
          refine ⟨3876779538746499118608281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10338078769990664316288749 3876779538746499118608281)
          ·
            refine ⟨2907584654059874338956211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3876779538746499118608281 2907584654059874338956211)
            ·
              refine ⟨4361376981089811508434317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907584654059874338956211 4361376981089811508434317)
              ·
                refine ⟨1635516367908679315662869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4361376981089811508434317 1635516367908679315662869)
                ·
                  refine ⟨76664829745719342921697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1635516367908679315662869 76664829745719342921697)
                  ·
                    rfl

theorem cell22_671869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_671869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671869 prefixEnd_671869 := by exact prefixLift 671869
  have htrace : WordTrace (prefixWord ++ tailWord_671869) baseStart_671869 baseEnd_671869 := by
    simpa [prefixWord, tailWord_671869, baseEnd_671869] using wordTrace_append hprefix tailTrace_671869
  have hstable : (prefixWord ++ tailWord_671869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671869).length < 2 ^ (prefixWord ++ tailWord_671869).sum := by decide
  have hdescent : baseEnd_671869 < baseStart_671869 := by decide
  rcases family_descends (prefixWord ++ tailWord_671869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671901 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_671901 : Nat := 118140960795 + 671901 * 2 ^ 59
def prefixEnd_671901 : Nat := 4983230072969 + 3 ^ 40 * 671901 * 2
def baseEnd_671901 : Nat := 230005443491120611964993

theorem tailTrace_671901 : CollatzResearch.WordTrace tailWord_671901 prefixEnd_671901 230005443491120611964993 := by
  unfold tailWord_671901
  simp only [CollatzResearch.WordTrace]
  refine ⟨24506242738824903400071557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16337495159216602266714371 24506242738824903400071557)
  ·
    refine ⟨4594920513529669387513417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24506242738824903400071557 4594920513529669387513417)
    ·
      refine ⟨3446190385147252040635063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4594920513529669387513417 3446190385147252040635063)
      ·
        refine ⟨5169285577720878060952595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446190385147252040635063 5169285577720878060952595)
        ·
          refine ⟨7753928366581317091428893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169285577720878060952595 7753928366581317091428893)
          ·
            refine ⟨2907723137467993909285835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7753928366581317091428893 2907723137467993909285835)
            ·
              refine ⟨4361584706201990863928753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907723137467993909285835 4361584706201990863928753)
              ·
                refine ⟨3271188529651493147946565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4361584706201990863928753 3271188529651493147946565)
                ·
                  refine ⟨613347849309654965239981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3271188529651493147946565 613347849309654965239981)
                  ·
                    refine ⟨230005443491120611964993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613347849309654965239981 230005443491120611964993)
                    ·
                      rfl

theorem cell22_671901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_671901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671901 prefixEnd_671901 := by exact prefixLift 671901
  have htrace : WordTrace (prefixWord ++ tailWord_671901) baseStart_671901 baseEnd_671901 := by
    simpa [prefixWord, tailWord_671901, baseEnd_671901] using wordTrace_append hprefix tailTrace_671901
  have hstable : (prefixWord ++ tailWord_671901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671901).length < 2 ^ (prefixWord ++ tailWord_671901).sum := by decide
  have hdescent : baseEnd_671901 < baseStart_671901 := by decide
  rcases family_descends (prefixWord ++ tailWord_671901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671903 : List Nat := [1, 1, 2, 6, 1, 1, 3, 3, 4]
def baseStart_671903 : Nat := 118140960795 + 671903 * 2 ^ 59
def prefixEnd_671903 : Nat := 4983230072969 + 3 ^ 40 * 671903 * 2
def baseEnd_671903 : Nat := 76668709377331091138329

theorem tailTrace_671903 : CollatzResearch.WordTrace tailWord_671903 prefixEnd_671903 76668709377331091138329 := by
  unfold tailWord_671903
  simp only [CollatzResearch.WordTrace]
  refine ⟨24506315684817657741644363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16337543789878438494429575 24506315684817657741644363)
  ·
    refine ⟨36759473527226486612466545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24506315684817657741644363 36759473527226486612466545)
    ·
      refine ⟨27569605145419864959349909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36759473527226486612466545 27569605145419864959349909)
      ·
        refine ⟨1292325241191556169969527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27569605145419864959349909 1292325241191556169969527)
        ·
          refine ⟨1938487861787334254954291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1292325241191556169969527 1938487861787334254954291)
          ·
            refine ⟨2907731792681001382431437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938487861787334254954291 2907731792681001382431437)
            ·
              refine ⟨1090399422255375518411789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2907731792681001382431437 1090399422255375518411789)
              ·
                refine ⟨408899783345765819404421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1090399422255375518411789 408899783345765819404421)
                ·
                  refine ⟨76668709377331091138329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408899783345765819404421 76668709377331091138329)
                  ·
                    rfl

theorem cell22_671903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 4].length) (baseStart_671903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671903 prefixEnd_671903 := by exact prefixLift 671903
  have htrace : WordTrace (prefixWord ++ tailWord_671903) baseStart_671903 baseEnd_671903 := by
    simpa [prefixWord, tailWord_671903, baseEnd_671903] using wordTrace_append hprefix tailTrace_671903
  have hstable : (prefixWord ++ tailWord_671903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671903).length < 2 ^ (prefixWord ++ tailWord_671903).sum := by decide
  have hdescent : baseEnd_671903 < baseStart_671903 := by decide
  rcases family_descends (prefixWord ++ tailWord_671903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671946 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_671946 : Nat := 118140960795 + 671946 * 2 ^ 59
def prefixEnd_671946 : Nat := 4983230072969 + 3 ^ 40 * 671946 * 2
def baseEnd_671946 : Nat := 230020847910755494589855

theorem tailTrace_671946 : CollatzResearch.WordTrace tailWord_671946 prefixEnd_671946 230020847910755494589855 := by
  unfold tailWord_671946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6126971005915469021364923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16338589349107917390306461 6126971005915469021364923)
  ·
    refine ⟨9190456508873203532047385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6126971005915469021364923 9190456508873203532047385)
    ·
      refine ⟨6892842381654902649035539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9190456508873203532047385 6892842381654902649035539)
      ·
        refine ⟨10339263572482353973553309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892842381654902649035539 10339263572482353973553309)
        ·
          refine ⟨3877223839680882740082491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10339263572482353973553309 3877223839680882740082491)
          ·
            refine ⟨5815835759521324110123737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877223839680882740082491 5815835759521324110123737)
            ·
              refine ⟨4361876819640993082592803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5815835759521324110123737 4361876819640993082592803)
              ·
                refine ⟨6542815229461489623889205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4361876819640993082592803 6542815229461489623889205)
                ·
                  refine ⟨613388927762014652239613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6542815229461489623889205 613388927762014652239613)
                  ·
                    refine ⟨230020847910755494589855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613388927762014652239613 230020847910755494589855)
                    ·
                      rfl

theorem cell22_671946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_671946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671946 prefixEnd_671946 := by exact prefixLift 671946
  have htrace : WordTrace (prefixWord ++ tailWord_671946) baseStart_671946 baseEnd_671946 := by
    simpa [prefixWord, tailWord_671946, baseEnd_671946] using wordTrace_append hprefix tailTrace_671946
  have hstable : (prefixWord ++ tailWord_671946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671946).length < 2 ^ (prefixWord ++ tailWord_671946).sum := by decide
  have hdescent : baseEnd_671946 < baseStart_671946 := by decide
  rcases family_descends (prefixWord ++ tailWord_671946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_671976 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 5]
def baseStart_671976 : Nat := 118140960795 + 671976 * 2 ^ 59
def prefixEnd_671976 : Nat := 4983230072969 + 3 ^ 40 * 671976 * 2
def baseEnd_671976 : Nat := 76677039174615138779921

theorem tailTrace_671976 : CollatzResearch.WordTrace tailWord_671976 prefixEnd_671976 76677039174615138779921 := by
  unfold tailWord_671976
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254489106776595604525891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16339318809035460806034521 12254489106776595604525891)
  ·
    refine ⟨18381733660164893406788837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12254489106776595604525891 18381733660164893406788837)
    ·
      refine ⟨3446575061280917513772907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18381733660164893406788837 3446575061280917513772907)
      ·
        refine ⟨5169862591921376270659361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446575061280917513772907 5169862591921376270659361)
        ·
          refine ⟨3877396943941032202994521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5169862591921376270659361 3877396943941032202994521)
          ·
            refine ⟨2908047707955774152245891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3877396943941032202994521 2908047707955774152245891)
            ·
              refine ⟨4362071561933661228368837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2908047707955774152245891 4362071561933661228368837)
              ·
                refine ⟨817888417862561480319157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4362071561933661228368837 817888417862561480319157)
                ·
                  refine ⟨76677039174615138779921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 817888417862561480319157 76677039174615138779921)
                  ·
                    rfl

theorem cell22_671976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_671976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_671976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_671976 prefixEnd_671976 := by exact prefixLift 671976
  have htrace : WordTrace (prefixWord ++ tailWord_671976) baseStart_671976 baseEnd_671976 := by
    simpa [prefixWord, tailWord_671976, baseEnd_671976] using wordTrace_append hprefix tailTrace_671976
  have hstable : (prefixWord ++ tailWord_671976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_671976).length < 2 ^ (prefixWord ++ tailWord_671976).sum := by decide
  have hdescent : baseEnd_671976 < baseStart_671976 := by decide
  rcases family_descends (prefixWord ++ tailWord_671976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672023 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 1, 4]
def baseStart_672023 : Nat := 118140960795 + 672023 * 2 ^ 59
def prefixEnd_672023 : Nat := 4983230072969 + 3 ^ 40 * 672023 * 2
def baseEnd_672023 : Nat := 230047206584352960414619

theorem tailTrace_672023 : CollatzResearch.WordTrace tailWord_672023 prefixEnd_672023 230047206584352960414619 := by
  unfold tailWord_672023
  simp only [CollatzResearch.WordTrace]
  refine ⟨24510692444382918236012723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16340461629588612157341815 24510692444382918236012723)
  ·
    refine ⟨36766038666574377354019085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24510692444382918236012723 36766038666574377354019085)
    ·
      refine ⟨13787264499965391507757157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36766038666574377354019085 13787264499965391507757157)
      ·
        refine ⟨2585112093743510907704467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13787264499965391507757157 2585112093743510907704467)
        ·
          refine ⟨3877668140615266361556701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585112093743510907704467 3877668140615266361556701)
          ·
            refine ⟨1454125552730724885583763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3877668140615266361556701 1454125552730724885583763)
            ·
              refine ⟨2181188329096087328375645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454125552730724885583763 2181188329096087328375645)
              ·
                refine ⟨817945623411032748140867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2181188329096087328375645 817945623411032748140867)
                ·
                  refine ⟨1226918435116549122211301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 817945623411032748140867 1226918435116549122211301)
                  ·
                    refine ⟨230047206584352960414619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1226918435116549122211301 230047206584352960414619)
                    ·
                      rfl

theorem cell22_672023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_672023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672023 prefixEnd_672023 := by exact prefixLift 672023
  have htrace : WordTrace (prefixWord ++ tailWord_672023) baseStart_672023 baseEnd_672023 := by
    simpa [prefixWord, tailWord_672023, baseEnd_672023] using wordTrace_append hprefix tailTrace_672023
  have hstable : (prefixWord ++ tailWord_672023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672023).length < 2 ^ (prefixWord ++ tailWord_672023).sum := by decide
  have hdescent : baseEnd_672023 < baseStart_672023 := by decide
  rcases family_descends (prefixWord ++ tailWord_672023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672190 : List Nat := [4, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_672190 : Nat := 118140960795 + 672190 * 2 ^ 59
def prefixEnd_672190 : Nat := 4983230072969 + 3 ^ 40 * 672190 * 2
def baseEnd_672190 : Nat := 76701458032406730496369

theorem tailTrace_672190 : CollatzResearch.WordTrace tailWord_672190 prefixEnd_672190 76701458032406730496369 := by
  unfold tailWord_672190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064597929347238219667753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16344522289851937171561349 3064597929347238219667753)
  ·
    refine ⟨2298448447010428664750815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3064597929347238219667753 2298448447010428664750815)
    ·
      refine ⟨3447672670515642997126223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2298448447010428664750815 3447672670515642997126223)
      ·
        refine ⟨5171509005773464495689335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3447672670515642997126223 5171509005773464495689335)
        ·
          refine ⟨7757263508660196743534003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5171509005773464495689335 7757263508660196743534003)
          ·
            refine ⟨11635895262990295115301005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7757263508660196743534003 11635895262990295115301005)
            ·
              refine ⟨4363460723621360668237877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11635895262990295115301005 4363460723621360668237877)
              ·
                refine ⟨409074442839502562647301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4363460723621360668237877 409074442839502562647301)
                ·
                  refine ⟨76701458032406730496369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409074442839502562647301 76701458032406730496369)
                  ·
                    rfl

theorem cell22_672190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_672190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672190 prefixEnd_672190 := by exact prefixLift 672190
  have htrace : WordTrace (prefixWord ++ tailWord_672190) baseStart_672190 baseEnd_672190 := by
    simpa [prefixWord, tailWord_672190, baseEnd_672190] using wordTrace_append hprefix tailTrace_672190
  have hstable : (prefixWord ++ tailWord_672190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672190).length < 2 ^ (prefixWord ++ tailWord_672190).sum := by decide
  have hdescent : baseEnd_672190 < baseStart_672190 := by decide
  rcases family_descends (prefixWord ++ tailWord_672190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672233 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 5, 3]
def baseStart_672233 : Nat := 118140960795 + 672233 * 2 ^ 59
def prefixEnd_672233 : Nat := 4983230072969 + 3 ^ 40 * 672233 * 2
def baseEnd_672233 : Nat := 230119093875982412663975

theorem tailTrace_672233 : CollatzResearch.WordTrace tailWord_672233 prefixEnd_672233 230119093875982412663975 := by
  unfold tailWord_672233
  simp only [CollatzResearch.WordTrace]
  refine ⟨24518351773622124101157353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16345567849081416067438235 24518351773622124101157353)
  ·
    refine ⟨18388763830216593075868015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24518351773622124101157353 18388763830216593075868015)
    ·
      refine ⟨27583145745324889613802023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18388763830216593075868015 27583145745324889613802023)
      ·
        refine ⟨41374718617987334420703035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27583145745324889613802023 41374718617987334420703035)
        ·
          refine ⟨62062077926981001631054553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41374718617987334420703035 62062077926981001631054553)
          ·
            refine ⟨46546558445235751223290915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62062077926981001631054553 46546558445235751223290915)
            ·
              refine ⟨69819837667853626834936373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46546558445235751223290915 69819837667853626834936373)
              ·
                refine ⟨6545609781361277515775285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69819837667853626834936373 6545609781361277515775285)
                ·
                  refine ⟨613650917002619767103933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6545609781361277515775285 613650917002619767103933)
                  ·
                    refine ⟨230119093875982412663975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613650917002619767103933 230119093875982412663975)
                    ·
                      rfl

theorem cell22_672233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_672233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672233 prefixEnd_672233 := by exact prefixLift 672233
  have htrace : WordTrace (prefixWord ++ tailWord_672233) baseStart_672233 baseEnd_672233 := by
    simpa [prefixWord, tailWord_672233, baseEnd_672233] using wordTrace_append hprefix tailTrace_672233
  have hstable : (prefixWord ++ tailWord_672233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672233).length < 2 ^ (prefixWord ++ tailWord_672233).sum := by decide
  have hdescent : baseEnd_672233 < baseStart_672233 := by decide
  rcases family_descends (prefixWord ++ tailWord_672233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672267 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 3, 3]
def baseStart_672267 : Nat := 118140960795 + 672267 * 2 ^ 59
def prefixEnd_672267 : Nat := 4983230072969 + 3 ^ 40 * 672267 * 2
def baseEnd_672267 : Nat := 230130732770817657313871

theorem tailTrace_672267 : CollatzResearch.WordTrace tailWord_672267 prefixEnd_672267 230130732770817657313871 := by
  unfold tailWord_672267
  simp only [CollatzResearch.WordTrace]
  refine ⟨24519591855498947907895055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16346394570332631938596703 24519591855498947907895055)
  ·
    refine ⟨36779387783248421861842583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24519591855498947907895055 36779387783248421861842583)
    ·
      refine ⟨55169081674872632792763875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36779387783248421861842583 55169081674872632792763875)
      ·
        refine ⟨82753622512308949189145813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55169081674872632792763875 82753622512308949189145813)
        ·
          refine ⟨1939538027632240996620605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 82753622512308949189145813 1939538027632240996620605)
          ·
            refine ⟨727326760362090373732727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1939538027632240996620605 727326760362090373732727)
            ·
              refine ⟨1090990140543135560599091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727326760362090373732727 1090990140543135560599091)
              ·
                refine ⟨1636485210814703340898637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1090990140543135560599091 1636485210814703340898637)
                ·
                  refine ⟨613681954055513752836989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1636485210814703340898637 613681954055513752836989)
                  ·
                    refine ⟨230130732770817657313871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613681954055513752836989 230130732770817657313871)
                    ·
                      rfl

theorem cell22_672267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 3].length) (baseStart_672267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672267 prefixEnd_672267 := by exact prefixLift 672267
  have htrace : WordTrace (prefixWord ++ tailWord_672267) baseStart_672267 baseEnd_672267 := by
    simpa [prefixWord, tailWord_672267, baseEnd_672267] using wordTrace_append hprefix tailTrace_672267
  have hstable : (prefixWord ++ tailWord_672267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672267).length < 2 ^ (prefixWord ++ tailWord_672267).sum := by decide
  have hdescent : baseEnd_672267 < baseStart_672267 := by decide
  rcases family_descends (prefixWord ++ tailWord_672267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672280 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 5]
def baseStart_672280 : Nat := 118140960795 + 672280 * 2 ^ 59
def prefixEnd_672280 : Nat := 4983230072969 + 3 ^ 40 * 672280 * 2
def baseEnd_672280 : Nat := 76711727645496652246277

theorem tailTrace_672280 : CollatzResearch.WordTrace tailWord_672280 prefixEnd_672280 76711727645496652246277 := by
  unfold tailWord_672280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260033002225925564059147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16346710669634567418745529 12260033002225925564059147)
  ·
    refine ⟨18390049503338888346088721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12260033002225925564059147 18390049503338888346088721)
    ·
      refine ⟨13792537127504166259566541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18390049503338888346088721 13792537127504166259566541)
      ·
        refine ⟨5172201422814062347337453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13792537127504166259566541 5172201422814062347337453)
        ·
          refine ⟨1939575533555273380251545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5172201422814062347337453 1939575533555273380251545)
          ·
            refine ⟨1454681650166455035188659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1939575533555273380251545 1454681650166455035188659)
            ·
              refine ⟨2182022475249682552782989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454681650166455035188659 2182022475249682552782989)
              ·
                refine ⟨818258428218630957293621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2182022475249682552782989 818258428218630957293621)
                ·
                  refine ⟨76711727645496652246277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 818258428218630957293621 76711727645496652246277)
                  ·
                    rfl

theorem cell22_672280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_672280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672280 prefixEnd_672280 := by exact prefixLift 672280
  have htrace : WordTrace (prefixWord ++ tailWord_672280) baseStart_672280 baseEnd_672280 := by
    simpa [prefixWord, tailWord_672280, baseEnd_672280] using wordTrace_append hprefix tailTrace_672280
  have hstable : (prefixWord ++ tailWord_672280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672280).length < 2 ^ (prefixWord ++ tailWord_672280).sum := by decide
  have hdescent : baseEnd_672280 < baseStart_672280 := by decide
  rcases family_descends (prefixWord ++ tailWord_672280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672340 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_672340 : Nat := 118140960795 + 672340 * 2 ^ 59
def prefixEnd_672340 : Nat := 4983230072969 + 3 ^ 40 * 672340 * 2
def baseEnd_672340 : Nat := 230155722162669800238647

theorem tailTrace_672340 : CollatzResearch.WordTrace tailWord_672340 prefixEnd_672340 230155722162669800238647 := by
  unfold tailWord_672340
  simp only [CollatzResearch.WordTrace]
  refine ⟨12261127192117240687651237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16348169589489654250201649 12261127192117240687651237)
  ·
    refine ⟨2298961348521982628934607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12261127192117240687651237 2298961348521982628934607)
    ·
      refine ⟨3448442022782973943401911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2298961348521982628934607 3448442022782973943401911)
      ·
        refine ⟨5172663034174460915102867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3448442022782973943401911 5172663034174460915102867)
        ·
          refine ⟨7758994551261691372654301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5172663034174460915102867 7758994551261691372654301)
          ·
            refine ⟨2909622956723134264745363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7758994551261691372654301 2909622956723134264745363)
            ·
              refine ⟨4364434435084701397118045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909622956723134264745363 4364434435084701397118045)
              ·
                refine ⟨1636662913156763023919267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4364434435084701397118045 1636662913156763023919267)
                ·
                  refine ⟨2454994369735144535878901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1636662913156763023919267 2454994369735144535878901)
                  ·
                    refine ⟨230155722162669800238647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2454994369735144535878901 230155722162669800238647)
                    ·
                      rfl

theorem cell22_672340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_672340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672340 prefixEnd_672340 := by exact prefixLift 672340
  have htrace : WordTrace (prefixWord ++ tailWord_672340) baseStart_672340 baseEnd_672340 := by
    simpa [prefixWord, tailWord_672340, baseEnd_672340] using wordTrace_append hprefix tailTrace_672340
  have hstable : (prefixWord ++ tailWord_672340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672340).length < 2 ^ (prefixWord ++ tailWord_672340).sum := by decide
  have hdescent : baseEnd_672340 < baseStart_672340 := by decide
  rcases family_descends (prefixWord ++ tailWord_672340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672370 : List Nat := [3, 2, 1, 2, 4, 1, 9]
def baseStart_672370 : Nat := 118140960795 + 672370 * 2 ^ 59
def prefixEnd_672370 : Nat := 4983230072969 + 3 ^ 40 * 672370 * 2
def baseEnd_672370 : Nat := 8524666362065174888465

theorem tailTrace_672370 : CollatzResearch.WordTrace tailWord_672370 prefixEnd_672370 8524666362065174888465 := by
  unfold tailWord_672370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6130837143531449124723641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16348899049417197665929709 6130837143531449124723641)
  ·
    refine ⟨4598127857648586843542731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6130837143531449124723641 4598127857648586843542731)
    ·
      refine ⟨6897191786472880265314097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4598127857648586843542731 6897191786472880265314097)
      ·
        refine ⟨5172893839854660198985573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6897191786472880265314097 5172893839854660198985573)
        ·
          refine ⟨969917594972748787309795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5172893839854660198985573 969917594972748787309795)
          ·
            refine ⟨1454876392459123180964693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969917594972748787309795 1454876392459123180964693)
            ·
              refine ⟨8524666362065174888465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1454876392459123180964693 8524666362065174888465)
              ·
                rfl

theorem cell22_672370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 9].length) (baseStart_672370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672370 prefixEnd_672370 := by exact prefixLift 672370
  have htrace : WordTrace (prefixWord ++ tailWord_672370) baseStart_672370 baseEnd_672370 := by
    simpa [prefixWord, tailWord_672370, baseEnd_672370] using wordTrace_append hprefix tailTrace_672370
  have hstable : (prefixWord ++ tailWord_672370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672370).length < 2 ^ (prefixWord ++ tailWord_672370).sum := by decide
  have hdescent : baseEnd_672370 < baseStart_672370 := by decide
  rcases family_descends (prefixWord ++ tailWord_672370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672374 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_672374 : Nat := 118140960795 + 672374 * 2 ^ 59
def prefixEnd_672374 : Nat := 4983230072969 + 3 ^ 40 * 672374 * 2
def baseEnd_672374 : Nat := 230167361057505044888543

theorem tailTrace_672374 : CollatzResearch.WordTrace tailWord_672374 prefixEnd_672374 230167361057505044888543 := by
  unfold tailWord_672374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1532718404131956573877511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16348996310740870121360117 1532718404131956573877511)
  ·
    refine ⟨2299077606197934860816267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1532718404131956573877511 2299077606197934860816267)
    ·
      refine ⟨3448616409296902291224401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299077606197934860816267 3448616409296902291224401)
      ·
        refine ⟨2586462306972676718418301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3448616409296902291224401 2586462306972676718418301)
        ·
          refine ⟨969923365114753769406863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2586462306972676718418301 969923365114753769406863)
          ·
            refine ⟨1454885047672130654110295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969923365114753769406863 1454885047672130654110295)
            ·
              refine ⟨2182327571508195981165443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454885047672130654110295 2182327571508195981165443)
              ·
                refine ⟨3273491357262293971748165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182327571508195981165443 3273491357262293971748165)
                ·
                  refine ⟨613779629486680119702781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3273491357262293971748165 613779629486680119702781)
                  ·
                    refine ⟨230167361057505044888543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613779629486680119702781 230167361057505044888543)
                    ·
                      rfl

theorem cell22_672374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_672374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672374 prefixEnd_672374 := by exact prefixLift 672374
  have htrace : WordTrace (prefixWord ++ tailWord_672374) baseStart_672374 baseEnd_672374 := by
    simpa [prefixWord, tailWord_672374, baseEnd_672374] using wordTrace_append hprefix tailTrace_672374
  have hstable : (prefixWord ++ tailWord_672374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672374).length < 2 ^ (prefixWord ++ tailWord_672374).sum := by decide
  have hdescent : baseEnd_672374 < baseStart_672374 := by decide
  rcases family_descends (prefixWord ++ tailWord_672374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672383 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 2, 6]
def baseStart_672383 : Nat := 118140960795 + 672383 * 2 ^ 59
def prefixEnd_672383 : Nat := 4983230072969 + 3 ^ 40 * 672383 * 2
def baseEnd_672383 : Nat := 230170441941432021413515

theorem tailTrace_672383 : CollatzResearch.WordTrace tailWord_672383 prefixEnd_672383 230170441941432021413515 := by
  unfold tailWord_672383
  simp only [CollatzResearch.WordTrace]
  refine ⟨24523822723078699719117803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16349215148719133146078535 24523822723078699719117803)
  ·
    refine ⟨36785734084618049578676705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24523822723078699719117803 36785734084618049578676705)
    ·
      refine ⟨27589300563463537184007529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36785734084618049578676705 27589300563463537184007529)
      ·
        refine ⟨20691975422597652888005647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27589300563463537184007529 20691975422597652888005647)
        ·
          refine ⟨31037963133896479332008471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20691975422597652888005647 31037963133896479332008471)
          ·
            refine ⟨46556944700844718998012707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31037963133896479332008471 46556944700844718998012707)
            ·
              refine ⟨69835417051267078497019061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46556944700844718998012707 69835417051267078497019061)
              ·
                refine ⟨6547070348556288609095537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69835417051267078497019061 6547070348556288609095537)
                ·
                  refine ⟨4910302761417216456821653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6547070348556288609095537 4910302761417216456821653)
                  ·
                    refine ⟨230170441941432021413515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4910302761417216456821653 230170441941432021413515)
                    ·
                      rfl

theorem cell22_672383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_672383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672383 prefixEnd_672383 := by exact prefixLift 672383
  have htrace : WordTrace (prefixWord ++ tailWord_672383) baseStart_672383 baseEnd_672383 := by
    simpa [prefixWord, tailWord_672383, baseEnd_672383] using wordTrace_append hprefix tailTrace_672383
  have hstable : (prefixWord ++ tailWord_672383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672383).length < 2 ^ (prefixWord ++ tailWord_672383).sum := by decide
  have hdescent : baseEnd_672383 < baseStart_672383 := by decide
  rcases family_descends (prefixWord ++ tailWord_672383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672404 : List Nat := [2, 4, 2, 2, 1, 3, 2, 6]
def baseStart_672404 : Nat := 118140960795 + 672404 * 2 ^ 59
def prefixEnd_672404 : Nat := 4983230072969 + 3 ^ 40 * 672404 * 2
def baseEnd_672404 : Nat := 25575292296732774070939

theorem tailTrace_672404 : CollatzResearch.WordTrace tailWord_672404 prefixEnd_672404 25575292296732774070939 := by
  unfold tailWord_672404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12262294328001310152816133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16349725770668413537088177 12262294328001310152816133)
  ·
    refine ⟨2299180186500245653653025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12262294328001310152816133 2299180186500245653653025)
    ·
      refine ⟨1724385139875184240239769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2299180186500245653653025 1724385139875184240239769)
      ·
        refine ⟨1293288854906388180179827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1724385139875184240239769 1293288854906388180179827)
        ·
          refine ⟨1939933282359582270269741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293288854906388180179827 1939933282359582270269741)
          ·
            refine ⟨727474980884843351351153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1939933282359582270269741 727474980884843351351153)
            ·
              refine ⟨545606235663632513513365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727474980884843351351153 545606235663632513513365)
              ·
                refine ⟨25575292296732774070939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 545606235663632513513365 25575292296732774070939)
                ·
                  rfl

theorem cell22_672404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 6].length) (baseStart_672404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672404 prefixEnd_672404 := by exact prefixLift 672404
  have htrace : WordTrace (prefixWord ++ tailWord_672404) baseStart_672404 baseEnd_672404 := by
    simpa [prefixWord, tailWord_672404, baseEnd_672404] using wordTrace_append hprefix tailTrace_672404
  have hstable : (prefixWord ++ tailWord_672404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672404).length < 2 ^ (prefixWord ++ tailWord_672404).sum := by decide
  have hdescent : baseEnd_672404 < baseStart_672404 := by decide
  rcases family_descends (prefixWord ++ tailWord_672404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672462 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_672462 : Nat := 118140960795 + 672462 * 2 ^ 59
def prefixEnd_672462 : Nat := 4983230072969 + 3 ^ 40 * 672462 * 2
def baseEnd_672462 : Nat := 230197485255902148688273

theorem tailTrace_672462 : CollatzResearch.WordTrace tailWord_672462 prefixEnd_672462 230197485255902148688273 := by
  unfold tailWord_672462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065838011224062026405455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16351136059861664140829093 3065838011224062026405455)
  ·
    refine ⟨4598757016836093039608183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3065838011224062026405455 4598757016836093039608183)
    ·
      refine ⟨6898135525254139559412275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4598757016836093039608183 6898135525254139559412275)
      ·
        refine ⟨10347203287881209339118413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6898135525254139559412275 10347203287881209339118413)
        ·
          refine ⟨3880201232955453502169405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10347203287881209339118413 3880201232955453502169405)
          ·
            refine ⟨1455075462358295063313527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3880201232955453502169405 1455075462358295063313527)
            ·
              refine ⟨2182613193537442594970291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455075462358295063313527 2182613193537442594970291)
              ·
                refine ⟨3273919790306163892455437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182613193537442594970291 3273919790306163892455437)
                ·
                  refine ⟨1227719921364811459670789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3273919790306163892455437 1227719921364811459670789)
                  ·
                    refine ⟨230197485255902148688273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1227719921364811459670789 230197485255902148688273)
                    ·
                      rfl

theorem cell22_672462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_672462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672462 prefixEnd_672462 := by exact prefixLift 672462
  have htrace : WordTrace (prefixWord ++ tailWord_672462) baseStart_672462 baseEnd_672462 := by
    simpa [prefixWord, tailWord_672462, baseEnd_672462] using wordTrace_append hprefix tailTrace_672462
  have hstable : (prefixWord ++ tailWord_672462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672462).length < 2 ^ (prefixWord ++ tailWord_672462).sum := by decide
  have hdescent : baseEnd_672462 < baseStart_672462 := by decide
  rcases family_descends (prefixWord ++ tailWord_672462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672479 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 1, 4]
def baseStart_672479 : Nat := 118140960795 + 672479 * 2 ^ 59
def prefixEnd_672479 : Nat := 4983230072969 + 3 ^ 40 * 672479 * 2
def baseEnd_672479 : Nat := 230203304703319771013221

theorem tailTrace_672479 : CollatzResearch.WordTrace tailWord_672479 prefixEnd_672479 230203304703319771013221 := by
  unfold tailWord_672479
  simp only [CollatzResearch.WordTrace]
  refine ⟨24527324130730908114612491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16351549420487272076408327 24527324130730908114612491)
  ·
    refine ⟨36790986196096362171918737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24527324130730908114612491 36790986196096362171918737)
    ·
      refine ⟨27593239647072271628939053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36790986196096362171918737 27593239647072271628939053)
      ·
        refine ⟨10347464867652101860852145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27593239647072271628939053 10347464867652101860852145)
        ·
          refine ⟨7760598650739076395639109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10347464867652101860852145 7760598650739076395639109)
          ·
            refine ⟨1455112247013576824182333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7760598650739076395639109 1455112247013576824182333)
            ·
              refine ⟨545667092630091309068375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1455112247013576824182333 545667092630091309068375)
              ·
                refine ⟨818500638945136963602563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545667092630091309068375 818500638945136963602563)
                ·
                  refine ⟨1227750958417705445403845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818500638945136963602563 1227750958417705445403845)
                  ·
                    refine ⟨230203304703319771013221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1227750958417705445403845 230203304703319771013221)
                    ·
                      rfl

theorem cell22_672479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 4].length) (baseStart_672479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672479 prefixEnd_672479 := by exact prefixLift 672479
  have htrace : WordTrace (prefixWord ++ tailWord_672479) baseStart_672479 baseEnd_672479 := by
    simpa [prefixWord, tailWord_672479, baseEnd_672479] using wordTrace_append hprefix tailTrace_672479
  have hstable : (prefixWord ++ tailWord_672479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672479).length < 2 ^ (prefixWord ++ tailWord_672479).sum := by decide
  have hdescent : baseEnd_672479 < baseStart_672479 := by decide
  rcases family_descends (prefixWord ++ tailWord_672479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672490 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_672490 : Nat := 118140960795 + 672490 * 2 ^ 59
def prefixEnd_672490 : Nat := 4983230072969 + 3 ^ 40 * 672490 * 2
def baseEnd_672490 : Nat := 230207070228119408988187

theorem tailTrace_672490 : CollatzResearch.WordTrace tailWord_672490 prefixEnd_672490 230207070228119408988187 := by
  unfold tailWord_672490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131931333422764248315731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16351816889127371328841949 6131931333422764248315731)
  ·
    refine ⟨9197897000134146372473597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6131931333422764248315731 9197897000134146372473597)
    ·
      refine ⟨3449211375050304889677599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9197897000134146372473597 3449211375050304889677599)
      ·
        refine ⟨5173817062575457334516399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449211375050304889677599 5173817062575457334516399)
        ·
          refine ⟨7760725593863186001774599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5173817062575457334516399 7760725593863186001774599)
          ·
            refine ⟨11641088390794779002661899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7760725593863186001774599 11641088390794779002661899)
            ·
              refine ⟨17461632586192168503992849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641088390794779002661899 17461632586192168503992849)
              ·
                refine ⟨13096224439644126377994637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17461632586192168503992849 13096224439644126377994637)
                ·
                  refine ⟨4911084164866547391747989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13096224439644126377994637 4911084164866547391747989)
                  ·
                    refine ⟨230207070228119408988187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4911084164866547391747989 230207070228119408988187)
                    ·
                      rfl

theorem cell22_672490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_672490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672490 prefixEnd_672490 := by exact prefixLift 672490
  have htrace : WordTrace (prefixWord ++ tailWord_672490) baseStart_672490 baseEnd_672490 := by
    simpa [prefixWord, tailWord_672490, baseEnd_672490] using wordTrace_append hprefix tailTrace_672490
  have hstable : (prefixWord ++ tailWord_672490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672490).length < 2 ^ (prefixWord ++ tailWord_672490).sum := by decide
  have hdescent : baseEnd_672490 < baseStart_672490 := by decide
  rcases family_descends (prefixWord ++ tailWord_672490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672494 : List Nat := [4, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_672494 : Nat := 118140960795 + 672494 * 2 ^ 59
def prefixEnd_672494 : Nat := 4983230072969 + 3 ^ 40 * 672494 * 2
def baseEnd_672494 : Nat := 76736146503288243962725

theorem tailTrace_672494 : CollatzResearch.WordTrace tailWord_672494 prefixEnd_672494 76736146503288243962725 := by
  unfold tailWord_672494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065983903209570709551067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16351914150451043784272357 3065983903209570709551067)
  ·
    refine ⟨4598975854814356064326601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3065983903209570709551067 4598975854814356064326601)
    ·
      refine ⟨3449231891110767048244951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4598975854814356064326601 3449231891110767048244951)
      ·
        refine ⟨5173847836666150572367427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449231891110767048244951 5173847836666150572367427)
        ·
          refine ⟨7760771754999225858551141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5173847836666150572367427 7760771754999225858551141)
          ·
            refine ⟨1455144704062354848478339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7760771754999225858551141 1455144704062354848478339)
            ·
              refine ⟨2182717056093532272717509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455144704062354848478339 2182717056093532272717509)
              ·
                refine ⟨409259448017537301134533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2182717056093532272717509 409259448017537301134533)
                ·
                  refine ⟨76736146503288243962725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409259448017537301134533 76736146503288243962725)
                  ·
                    rfl

theorem cell22_672494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_672494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672494 prefixEnd_672494 := by exact prefixLift 672494
  have htrace : WordTrace (prefixWord ++ tailWord_672494) baseStart_672494 baseEnd_672494 := by
    simpa [prefixWord, tailWord_672494, baseEnd_672494] using wordTrace_append hprefix tailTrace_672494
  have hstable : (prefixWord ++ tailWord_672494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672494).length < 2 ^ (prefixWord ++ tailWord_672494).sum := by decide
  have hdescent : baseEnd_672494 < baseStart_672494 := by decide
  rcases family_descends (prefixWord ++ tailWord_672494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672522 : List Nat := [3, 1, 2, 2, 1, 2, 5, 6]
def baseStart_672522 : Nat := 118140960795 + 672522 * 2 ^ 59
def prefixEnd_672522 : Nat := 4983230072969 + 3 ^ 40 * 672522 * 2
def baseEnd_672522 : Nat := 25579780498009110243121

theorem tailTrace_672522 : CollatzResearch.WordTrace tailWord_672522 prefixEnd_672522 25579780498009110243121 := by
  unfold tailWord_672522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132223117393781614606955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16352594979716750972285213 6132223117393781614606955)
  ·
    refine ⟨9198334676090672421910433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6132223117393781614606955 9198334676090672421910433)
    ·
      refine ⟨6898751007068004316432825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9198334676090672421910433 6898751007068004316432825)
      ·
        refine ⟨5174063255301003237324619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6898751007068004316432825 5174063255301003237324619)
        ·
          refine ⟨7761094882951504855986929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174063255301003237324619 7761094882951504855986929)
          ·
            refine ⟨5820821162213628641990197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7761094882951504855986929 5820821162213628641990197)
            ·
              refine ⟨545701983957527685186581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5820821162213628641990197 545701983957527685186581)
              ·
                refine ⟨25579780498009110243121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 545701983957527685186581 25579780498009110243121)
                ·
                  rfl

theorem cell22_672522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_672522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672522 prefixEnd_672522 := by exact prefixLift 672522
  have htrace : WordTrace (prefixWord ++ tailWord_672522) baseStart_672522 baseEnd_672522 := by
    simpa [prefixWord, tailWord_672522, baseEnd_672522] using wordTrace_append hprefix tailTrace_672522
  have hstable : (prefixWord ++ tailWord_672522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672522).length < 2 ^ (prefixWord ++ tailWord_672522).sum := by decide
  have hdescent : baseEnd_672522 < baseStart_672522 := by decide
  rcases family_descends (prefixWord ++ tailWord_672522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672530 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_672530 : Nat := 118140960795 + 672530 * 2 ^ 59
def prefixEnd_672530 : Nat := 4983230072969 + 3 ^ 40 * 672530 * 2
def baseEnd_672530 : Nat := 230220763045572637988065

theorem tailTrace_672530 : CollatzResearch.WordTrace tailWord_672530 prefixEnd_672530 230220763045572637988065 := by
  unfold tailWord_672530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132296063386535956179761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16352789502364095883146029 6132296063386535956179761)
  ·
    refine ⟨4599222047539901967134821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6132296063386535956179761 4599222047539901967134821)
    ·
      refine ⟨862354133913731618837779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4599222047539901967134821 862354133913731618837779)
      ·
        refine ⟨1293531200870597428256669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862354133913731618837779 1293531200870597428256669)
        ·
          refine ⟨485074200326474035596251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1293531200870597428256669 485074200326474035596251)
          ·
            refine ⟨727611300489711053394377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485074200326474035596251 727611300489711053394377)
            ·
              refine ⟨545708475367283290045783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727611300489711053394377 545708475367283290045783)
              ·
                refine ⟨818562713050924935068675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545708475367283290045783 818562713050924935068675)
                ·
                  refine ⟨1227844069576387402603013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818562713050924935068675 1227844069576387402603013)
                  ·
                    refine ⟨230220763045572637988065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1227844069576387402603013 230220763045572637988065)
                    ·
                      rfl

theorem cell22_672530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_672530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672530 prefixEnd_672530 := by exact prefixLift 672530
  have htrace : WordTrace (prefixWord ++ tailWord_672530) baseStart_672530 baseEnd_672530 := by
    simpa [prefixWord, tailWord_672530, baseEnd_672530] using wordTrace_append hprefix tailTrace_672530
  have hstable : (prefixWord ++ tailWord_672530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672530).length < 2 ^ (prefixWord ++ tailWord_672530).sum := by decide
  have hdescent : baseEnd_672530 < baseStart_672530 := by decide
  rcases family_descends (prefixWord ++ tailWord_672530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672588 : List Nat := [2, 2, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_672588 : Nat := 118140960795 + 672588 * 2 ^ 59
def prefixEnd_672588 : Nat := 4983230072969 + 3 ^ 40 * 672588 * 2
def baseEnd_672588 : Nat := 230240617630879820037887

theorem tailTrace_672588 : CollatzResearch.WordTrace tailWord_672588 prefixEnd_672588 230240617630879820037887 := by
  unfold tailWord_672588
  simp only [CollatzResearch.WordTrace]
  refine ⟨12265649843668009865165209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16354199791557346486886945 12265649843668009865165209)
  ·
    refine ⟨9199237382751007398873907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12265649843668009865165209 9199237382751007398873907)
    ·
      refine ⟨13798856074126511098310861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9199237382751007398873907 13798856074126511098310861)
      ·
        refine ⟨5174571027797441661866573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13798856074126511098310861 5174571027797441661866573)
        ·
          refine ⟨1940464135424040623199965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5174571027797441661866573 1940464135424040623199965)
          ·
            refine ⟨727674050784015233699987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1940464135424040623199965 727674050784015233699987)
            ·
              refine ⟨1091511076176022850549981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727674050784015233699987 1091511076176022850549981)
              ·
                refine ⟨409316653566008568956243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1091511076176022850549981 409316653566008568956243)
                ·
                  refine ⟨613974980349012853434365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409316653566008568956243 613974980349012853434365)
                  ·
                    refine ⟨230240617630879820037887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 613974980349012853434365 230240617630879820037887)
                    ·
                      rfl

theorem cell22_672588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_672588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672588 prefixEnd_672588 := by exact prefixLift 672588
  have htrace : WordTrace (prefixWord ++ tailWord_672588) baseStart_672588 baseEnd_672588 := by
    simpa [prefixWord, tailWord_672588, baseEnd_672588] using wordTrace_append hprefix tailTrace_672588
  have hstable : (prefixWord ++ tailWord_672588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672588).length < 2 ^ (prefixWord ++ tailWord_672588).sum := by decide
  have hdescent : baseEnd_672588 < baseStart_672588 := by decide
  rcases family_descends (prefixWord ++ tailWord_672588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672595 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 8]
def baseStart_672595 : Nat := 118140960795 + 672595 * 2 ^ 59
def prefixEnd_672595 : Nat := 4983230072969 + 3 ^ 40 * 672595 * 2
def baseEnd_672595 : Nat := 76747671291311378370955

theorem tailTrace_672595 : CollatzResearch.WordTrace tailWord_672595 prefixEnd_672595 76747671291311378370955 := by
  unfold tailWord_672595
  simp only [CollatzResearch.WordTrace]
  refine ⟨24531554998310659925835239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16354369998873773283890159 24531554998310659925835239)
  ·
    refine ⟨36797332497465989888752859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24531554998310659925835239 36797332497465989888752859)
    ·
      refine ⟨55195998746198984833129289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36797332497465989888752859 55195998746198984833129289)
      ·
        refine ⟨41396999059649238624846967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55195998746198984833129289 41396999059649238624846967)
        ·
          refine ⟨62095498589473857937270451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41396999059649238624846967 62095498589473857937270451)
          ·
            refine ⟨93143247884210786905905677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62095498589473857937270451 93143247884210786905905677)
            ·
              refine ⟨34928717956579045089714629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93143247884210786905905677 34928717956579045089714629)
              ·
                refine ⟨6549134616858570954321493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34928717956579045089714629 6549134616858570954321493)
                ·
                  refine ⟨76747671291311378370955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6549134616858570954321493 76747671291311378370955)
                  ·
                    rfl

theorem cell22_672595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 8].length) (baseStart_672595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672595 prefixEnd_672595 := by exact prefixLift 672595
  have htrace : WordTrace (prefixWord ++ tailWord_672595) baseStart_672595 baseEnd_672595 := by
    simpa [prefixWord, tailWord_672595, baseEnd_672595] using wordTrace_append hprefix tailTrace_672595
  have hstable : (prefixWord ++ tailWord_672595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672595).length < 2 ^ (prefixWord ++ tailWord_672595).sum := by decide
  have hdescent : baseEnd_672595 < baseStart_672595 := by decide
  rcases family_descends (prefixWord ++ tailWord_672595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672661 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_672661 : Nat := 118140960795 + 672661 * 2 ^ 59
def prefixEnd_672661 : Nat := 4983230072969 + 3 ^ 40 * 672661 * 2
def baseEnd_672661 : Nat := 230265607022731962962663

theorem tailTrace_672661 : CollatzResearch.WordTrace tailWord_672661 prefixEnd_672661 230265607022731962962663 := by
  unfold tailWord_672661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24533962216071553197737837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16355974810714368798491891 24533962216071553197737837)
  ·
    refine ⟨9200235831026832449151689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24533962216071553197737837 9200235831026832449151689)
    ·
      refine ⟨6900176873270124336863767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9200235831026832449151689 6900176873270124336863767)
      ·
        refine ⟨10350265309905186505295651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6900176873270124336863767 10350265309905186505295651)
        ·
          refine ⟨15525397964857779757943477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10350265309905186505295651 15525397964857779757943477)
          ·
            refine ⟨1455506059205416852307201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15525397964857779757943477 1455506059205416852307201)
            ·
              refine ⟨1091629544404062639230401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455506059205416852307201 1091629544404062639230401)
              ·
                refine ⟨818722158303046979422801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091629544404062639230401 818722158303046979422801)
                ·
                  refine ⟨614041618727285234567101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 818722158303046979422801 614041618727285234567101)
                  ·
                    refine ⟨230265607022731962962663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 614041618727285234567101 230265607022731962962663)
                    ·
                      rfl

theorem cell22_672661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_672661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672661 prefixEnd_672661 := by exact prefixLift 672661
  have htrace : WordTrace (prefixWord ++ tailWord_672661) baseStart_672661 baseEnd_672661 := by
    simpa [prefixWord, tailWord_672661, baseEnd_672661] using wordTrace_append hprefix tailTrace_672661
  have hstable : (prefixWord ++ tailWord_672661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672661).length < 2 ^ (prefixWord ++ tailWord_672661).sum := by decide
  have hdescent : baseEnd_672661 < baseStart_672661 := by decide
  rcases family_descends (prefixWord ++ tailWord_672661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672674 : List Nat := [3, 3, 1, 2, 2, 1, 3, 7]
def baseStart_672674 : Nat := 118140960795 + 672674 * 2 ^ 59
def prefixEnd_672674 : Nat := 4983230072969 + 3 ^ 40 * 672674 * 2
def baseEnd_672674 : Nat := 25585561909822695820847

theorem tailTrace_672674 : CollatzResearch.WordTrace tailWord_672674 prefixEnd_672674 25585561909822695820847 := by
  unfold tailWord_672674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6133609091256114104490269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16356290910016304278640717 6133609091256114104490269)
  ·
    refine ⟨2300103409221042789183851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6133609091256114104490269 2300103409221042789183851)
    ·
      refine ⟨3450155113831564183775777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2300103409221042789183851 3450155113831564183775777)
      ·
        refine ⟨2587616335373673137831833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3450155113831564183775777 2587616335373673137831833)
        ·
          refine ⟨1940712251530254853373875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2587616335373673137831833 1940712251530254853373875)
          ·
            refine ⟨2911068377295382280060813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940712251530254853373875 2911068377295382280060813)
            ·
              refine ⟨1091650641485768355022805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2911068377295382280060813 1091650641485768355022805)
              ·
                refine ⟨25585561909822695820847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1091650641485768355022805 25585561909822695820847)
                ·
                  rfl

theorem cell22_672674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_672674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672674 prefixEnd_672674 := by exact prefixLift 672674
  have htrace : WordTrace (prefixWord ++ tailWord_672674) baseStart_672674 baseEnd_672674 := by
    simpa [prefixWord, tailWord_672674, baseEnd_672674] using wordTrace_append hprefix tailTrace_672674
  have hstable : (prefixWord ++ tailWord_672674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672674).length < 2 ^ (prefixWord ++ tailWord_672674).sum := by decide
  have hdescent : baseEnd_672674 < baseStart_672674 := by decide
  rcases family_descends (prefixWord ++ tailWord_672674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672719 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 5]
def baseStart_672719 : Nat := 118140960795 + 672719 * 2 ^ 59
def prefixEnd_672719 : Nat := 4983230072969 + 3 ^ 40 * 672719 * 2
def baseEnd_672719 : Nat := 76761820536013048337495

theorem tailTrace_672719 : CollatzResearch.WordTrace tailWord_672719 prefixEnd_672719 76761820536013048337495 := by
  unfold tailWord_672719
  simp only [CollatzResearch.WordTrace]
  refine ⟨24536077649861429103349211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16357385099907619402232807 24536077649861429103349211)
  ·
    refine ⟨36804116474792143655023817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24536077649861429103349211 36804116474792143655023817)
    ·
      refine ⟨27603087356094107741267863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36804116474792143655023817 27603087356094107741267863)
      ·
        refine ⟨41404631034141161611901795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27603087356094107741267863 41404631034141161611901795)
        ·
          refine ⟨62106946551211742417852693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41404631034141161611901795 62106946551211742417852693)
          ·
            refine ⟨2911263119588050425836845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62106946551211742417852693 2911263119588050425836845)
            ·
              refine ⟨1091723669845518909688817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2911263119588050425836845 1091723669845518909688817)
              ·
                refine ⟨818792752384139182266613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091723669845518909688817 818792752384139182266613)
                ·
                  refine ⟨76761820536013048337495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 818792752384139182266613 76761820536013048337495)
                  ·
                    rfl

theorem cell22_672719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 5].length) (baseStart_672719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672719 prefixEnd_672719 := by exact prefixLift 672719
  have htrace : WordTrace (prefixWord ++ tailWord_672719) baseStart_672719 baseEnd_672719 := by
    simpa [prefixWord, tailWord_672719, baseEnd_672719] using wordTrace_append hprefix tailTrace_672719
  have hstable : (prefixWord ++ tailWord_672719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672719).length < 2 ^ (prefixWord ++ tailWord_672719).sum := by decide
  have hdescent : baseEnd_672719 < baseStart_672719 := by decide
  rcases family_descends (prefixWord ++ tailWord_672719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672794 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_672794 : Nat := 118140960795 + 672794 * 2 ^ 59
def prefixEnd_672794 : Nat := 4983230072969 + 3 ^ 40 * 672794 * 2
def baseEnd_672794 : Nat := 230311135640763949387255

theorem tailTrace_672794 : CollatzResearch.WordTrace tailWord_672794 prefixEnd_672794 230311135640763949387255 := by
  unfold tailWord_672794
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134703281147429228082359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16359208749726477941552957 6134703281147429228082359)
  ·
    refine ⟨9202054921721143842123539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6134703281147429228082359 9202054921721143842123539)
    ·
      refine ⟨13803082382581715763185309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9202054921721143842123539 13803082382581715763185309)
      ·
        refine ⟨5176155893468143411194491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13803082382581715763185309 5176155893468143411194491)
        ·
          refine ⟨7764233840202215116791737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5176155893468143411194491 7764233840202215116791737)
          ·
            refine ⟨5823175380151661337593803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7764233840202215116791737 5823175380151661337593803)
            ·
              refine ⟨8734763070227492006390705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823175380151661337593803 8734763070227492006390705)
              ·
                refine ⟨6551072302670619004793029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8734763070227492006390705 6551072302670619004793029)
                ·
                  refine ⟨1228326056750741063398693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6551072302670619004793029 1228326056750741063398693)
                  ·
                    refine ⟨230311135640763949387255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1228326056750741063398693 230311135640763949387255)
                    ·
                      rfl

theorem cell22_672794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_672794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672794 prefixEnd_672794 := by exact prefixLift 672794
  have htrace : WordTrace (prefixWord ++ tailWord_672794) baseStart_672794 baseEnd_672794 := by
    simpa [prefixWord, tailWord_672794, baseEnd_672794] using wordTrace_append hprefix tailTrace_672794
  have hstable : (prefixWord ++ tailWord_672794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672794).length < 2 ^ (prefixWord ++ tailWord_672794).sum := by decide
  have hdescent : baseEnd_672794 < baseStart_672794 := by decide
  rcases family_descends (prefixWord ++ tailWord_672794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672800 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 1, 4]
def baseStart_672800 : Nat := 118140960795 + 672800 * 2 ^ 59
def prefixEnd_672800 : Nat := 4983230072969 + 3 ^ 40 * 672800 * 2
def baseEnd_672800 : Nat := 230313189563381933737237

theorem tailTrace_672800 : CollatzResearch.WordTrace tailWord_672800 prefixEnd_672800 230313189563381933737237 := by
  unfold tailWord_672800
  simp only [CollatzResearch.WordTrace]
  refine ⟨12269515981283989968523927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16359354641711986624698569 12269515981283989968523927)
  ·
    refine ⟨18404273971925984952785891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12269515981283989968523927 18404273971925984952785891)
    ·
      refine ⟨27606410957888977429178837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18404273971925984952785891 27606410957888977429178837)
      ·
        refine ⟨647025256825522908496379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 27606410957888977429178837 647025256825522908496379)
        ·
          refine ⟨970537885238284362744569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647025256825522908496379 970537885238284362744569)
          ·
            refine ⟨727903413928713272058427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 970537885238284362744569 727903413928713272058427)
            ·
              refine ⟨1091855120893069908087641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727903413928713272058427 1091855120893069908087641)
              ·
                refine ⟨818891340669802431065731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091855120893069908087641 818891340669802431065731)
                ·
                  refine ⟨1228337011004703646598597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 818891340669802431065731 1228337011004703646598597)
                  ·
                    refine ⟨230313189563381933737237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1228337011004703646598597 230313189563381933737237)
                    ·
                      rfl

theorem cell22_672800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_672800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672800 prefixEnd_672800 := by exact prefixLift 672800
  have htrace : WordTrace (prefixWord ++ tailWord_672800) baseStart_672800 baseEnd_672800 := by
    simpa [prefixWord, tailWord_672800, baseEnd_672800] using wordTrace_append hprefix tailTrace_672800
  have hstable : (prefixWord ++ tailWord_672800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672800).length < 2 ^ (prefixWord ++ tailWord_672800).sum := by decide
  have hdescent : baseEnd_672800 < baseStart_672800 := by decide
  rcases family_descends (prefixWord ++ tailWord_672800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672830 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_672830 : Nat := 118140960795 + 672830 * 2 ^ 59
def prefixEnd_672830 : Nat := 4983230072969 + 3 ^ 40 * 672830 * 2
def baseEnd_672830 : Nat := 230323459176471855487145

theorem tailTrace_672830 : CollatzResearch.WordTrace tailWord_672830 prefixEnd_672830 230323459176471855487145 := by
  unfold tailWord_672830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067515769057411882579993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16360084101639530040426629 3067515769057411882579993)
  ·
    refine ⟨2300636826793058911934995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3067515769057411882579993 2300636826793058911934995)
    ·
      refine ⟨3450955240189588367902493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2300636826793058911934995 3450955240189588367902493)
      ·
        refine ⟨1294108215071095637963435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3450955240189588367902493 1294108215071095637963435)
        ·
          refine ⟨1941162322606643456945153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294108215071095637963435 1941162322606643456945153)
          ·
            refine ⟨1455871741954982592708865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941162322606643456945153 1455871741954982592708865)
            ·
              refine ⟨1091903806466236944531649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455871741954982592708865 1091903806466236944531649)
              ·
                refine ⟨818927854849677708398737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091903806466236944531649 818927854849677708398737)
                ·
                  refine ⟨614195891137258281299053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 818927854849677708398737 614195891137258281299053)
                  ·
                    refine ⟨230323459176471855487145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 614195891137258281299053 230323459176471855487145)
                    ·
                      rfl

theorem cell22_672830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_672830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672830 prefixEnd_672830 := by exact prefixLift 672830
  have htrace : WordTrace (prefixWord ++ tailWord_672830) baseStart_672830 baseEnd_672830 := by
    simpa [prefixWord, tailWord_672830, baseEnd_672830] using wordTrace_append hprefix tailTrace_672830
  have hstable : (prefixWord ++ tailWord_672830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672830).length < 2 ^ (prefixWord ++ tailWord_672830).sum := by decide
  have hdescent : baseEnd_672830 < baseStart_672830 := by decide
  rcases family_descends (prefixWord ++ tailWord_672830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672839 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 2, 6]
def baseStart_672839 : Nat := 118140960795 + 672839 * 2 ^ 59
def prefixEnd_672839 : Nat := 4983230072969 + 3 ^ 40 * 672839 * 2
def baseEnd_672839 : Nat := 230326540060398832012117

theorem tailTrace_672839 : CollatzResearch.WordTrace tailWord_672839 prefixEnd_672839 230326540060398832012117 := by
  unfold tailWord_672839
  simp only [CollatzResearch.WordTrace]
  refine ⟨24540454409426689597717571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16360302939617793065145047 24540454409426689597717571)
  ·
    refine ⟨36810681614140034396576357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24540454409426689597717571 36810681614140034396576357)
    ·
      refine ⟨6902002802651256449358067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36810681614140034396576357 6902002802651256449358067)
      ·
        refine ⟨10353004203976884674037101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6902002802651256449358067 10353004203976884674037101)
        ·
          refine ⟨3882376576491331752763913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10353004203976884674037101 3882376576491331752763913)
          ·
            refine ⟨2911782432368498814572935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3882376576491331752763913 2911782432368498814572935)
            ·
              refine ⟨4367673648552748221859403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911782432368498814572935 4367673648552748221859403)
              ·
                refine ⟨6551510472829122332789105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4367673648552748221859403 6551510472829122332789105)
                ·
                  refine ⟨4913632854621841749591829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6551510472829122332789105 4913632854621841749591829)
                  ·
                    refine ⟨230326540060398832012117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4913632854621841749591829 230326540060398832012117)
                    ·
                      rfl

theorem cell22_672839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_672839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672839 prefixEnd_672839 := by exact prefixLift 672839
  have htrace : WordTrace (prefixWord ++ tailWord_672839) baseStart_672839 baseEnd_672839 := by
    simpa [prefixWord, tailWord_672839, baseEnd_672839] using wordTrace_append hprefix tailTrace_672839
  have hstable : (prefixWord ++ tailWord_672839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672839).length < 2 ^ (prefixWord ++ tailWord_672839).sum := by decide
  have hdescent : baseEnd_672839 < baseStart_672839 := by decide
  rcases family_descends (prefixWord ++ tailWord_672839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672862 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_672862 : Nat := 118140960795 + 672862 * 2 ^ 59
def prefixEnd_672862 : Nat := 4983230072969 + 3 ^ 40 * 672862 * 2
def baseEnd_672862 : Nat := 230334413430434438687047

theorem tailTrace_672862 : CollatzResearch.WordTrace tailWord_672862 prefixEnd_672862 230334413430434438687047 := by
  unfold tailWord_672862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067661661042920565725605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16360862192228909683869893 3067661661042920565725605)
  ·
    refine ⟨575186561445547606073551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3067661661042920565725605 575186561445547606073551)
    ·
      refine ⟨862779842168321409110327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575186561445547606073551 862779842168321409110327)
      ·
        refine ⟨1294169763252482113665491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862779842168321409110327 1294169763252482113665491)
        ·
          refine ⟨1941254644878723170498237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294169763252482113665491 1941254644878723170498237)
          ·
            refine ⟨727970491829521188936839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1941254644878723170498237 727970491829521188936839)
            ·
              refine ⟨1091955737744281783405259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727970491829521188936839 1091955737744281783405259)
              ·
                refine ⟨1637933606616422675107889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091955737744281783405259 1637933606616422675107889)
                ·
                  refine ⟨1228450204962317006330917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1637933606616422675107889 1228450204962317006330917)
                  ·
                    refine ⟨230334413430434438687047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1228450204962317006330917 230334413430434438687047)
                    ·
                      rfl

theorem cell22_672862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_672862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672862 prefixEnd_672862 := by exact prefixLift 672862
  have htrace : WordTrace (prefixWord ++ tailWord_672862) baseStart_672862 baseEnd_672862 := by
    simpa [prefixWord, tailWord_672862, baseEnd_672862] using wordTrace_append hprefix tailTrace_672862
  have hstable : (prefixWord ++ tailWord_672862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672862).length < 2 ^ (prefixWord ++ tailWord_672862).sum := by decide
  have hdescent : baseEnd_672862 < baseStart_672862 := by decide
  rcases family_descends (prefixWord ++ tailWord_672862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672869 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_672869 : Nat := 118140960795 + 672869 * 2 ^ 59
def prefixEnd_672869 : Nat := 4983230072969 + 3 ^ 40 * 672869 * 2
def baseEnd_672869 : Nat := 230336809673488753762025

theorem tailTrace_672869 : CollatzResearch.WordTrace tailWord_672869 prefixEnd_672869 230336809673488753762025 := by
  unfold tailWord_672869
  simp only [CollatzResearch.WordTrace]
  refine ⟨24541548599318004721309661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16361032399545336480873107 24541548599318004721309661)
  ·
    refine ⟨9203080724744251770491123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24541548599318004721309661 9203080724744251770491123)
    ·
      refine ⟨13804621087116377655736685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9203080724744251770491123 13804621087116377655736685)
      ·
        refine ⟨5176732907668641620901257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13804621087116377655736685 5176732907668641620901257)
        ·
          refine ⟨3882549680751481215675943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5176732907668641620901257 3882549680751481215675943)
          ·
            refine ⟨5823824521127221823513915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882549680751481215675943 5823824521127221823513915)
            ·
              refine ⟨8735736781690832735270873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823824521127221823513915 8735736781690832735270873)
              ·
                refine ⟨6551802586268124551453155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8735736781690832735270873 6551802586268124551453155)
                ·
                  refine ⟨9827703879402186827179733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6551802586268124551453155 9827703879402186827179733)
                  ·
                    refine ⟨230336809673488753762025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9827703879402186827179733 230336809673488753762025)
                    ·
                      rfl

theorem cell22_672869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_672869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672869 prefixEnd_672869 := by exact prefixLift 672869
  have htrace : WordTrace (prefixWord ++ tailWord_672869) baseStart_672869 baseEnd_672869 := by
    simpa [prefixWord, tailWord_672869, baseEnd_672869] using wordTrace_append hprefix tailTrace_672869
  have hstable : (prefixWord ++ tailWord_672869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672869).length < 2 ^ (prefixWord ++ tailWord_672869).sum := by decide
  have hdescent : baseEnd_672869 < baseStart_672869 := by decide
  rcases family_descends (prefixWord ++ tailWord_672869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672886 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_672886 : Nat := 118140960795 + 672886 * 2 ^ 59
def prefixEnd_672886 : Nat := 4983230072969 + 3 ^ 40 * 672886 * 2
def baseEnd_672886 : Nat := 230342629120906376086973

theorem tailTrace_672886 : CollatzResearch.WordTrace tailWord_672886 prefixEnd_672886 230342629120906376086973 := by
  unfold tailWord_672886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533885540016026039042407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16361445760170944416452341 1533885540016026039042407)
  ·
    refine ⟨2300828310024039058563611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1533885540016026039042407 2300828310024039058563611)
    ·
      refine ⟨3451242465036058587845417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2300828310024039058563611 3451242465036058587845417)
      ·
        refine ⟨2588431848777043940884063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3451242465036058587845417 2588431848777043940884063)
        ·
          refine ⟨3882647773165565911326095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588431848777043940884063 3882647773165565911326095)
          ·
            refine ⟨5823971659748348866989143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3882647773165565911326095 5823971659748348866989143)
            ·
              refine ⟨8735957489622523300483715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5823971659748348866989143 8735957489622523300483715)
              ·
                refine ⟨13103936234433784950725573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8735957489622523300483715 13103936234433784950725573)
                ·
                  refine ⟨2456988043956334678261045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13103936234433784950725573 2456988043956334678261045)
                  ·
                    refine ⟨230342629120906376086973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2456988043956334678261045 230342629120906376086973)
                    ·
                      rfl

theorem cell22_672886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_672886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672886 prefixEnd_672886 := by exact prefixLift 672886
  have htrace : WordTrace (prefixWord ++ tailWord_672886) baseStart_672886 baseEnd_672886 := by
    simpa [prefixWord, tailWord_672886, baseEnd_672886] using wordTrace_append hprefix tailTrace_672886
  have hstable : (prefixWord ++ tailWord_672886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672886).length < 2 ^ (prefixWord ++ tailWord_672886).sum := by decide
  have hdescent : baseEnd_672886 < baseStart_672886 := by decide
  rcases family_descends (prefixWord ++ tailWord_672886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672933 : List Nat := [1, 3, 1, 2, 1, 4, 3, 3, 4]
def baseStart_672933 : Nat := 118140960795 + 672933 * 2 ^ 59
def prefixEnd_672933 : Nat := 4983230072969 + 3 ^ 40 * 672933 * 2
def baseEnd_672933 : Nat := 76786239393804640053943

theorem tailTrace_672933 : CollatzResearch.WordTrace tailWord_672933 prefixEnd_672933 76786239393804640053943 := by
  unfold tailWord_672933
  simp only [CollatzResearch.WordTrace]
  refine ⟨24543882871086143651639453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16362588580724095767759635 24543882871086143651639453)
  ·
    refine ⟨9203956076657303869364795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24543882871086143651639453 9203956076657303869364795)
    ·
      refine ⟨13805934114985955804047193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9203956076657303869364795 13805934114985955804047193)
      ·
        refine ⟨10354450586239466853035395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13805934114985955804047193 10354450586239466853035395)
        ·
          refine ⟨15531675879359200279553093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10354450586239466853035395 15531675879359200279553093)
          ·
            refine ⟨2912189227379850052416205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15531675879359200279553093 2912189227379850052416205)
            ·
              refine ⟨1092070960267443769656077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2912189227379850052416205 1092070960267443769656077)
              ·
                refine ⟨409526610100291413621029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1092070960267443769656077 409526610100291413621029)
                ·
                  refine ⟨76786239393804640053943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409526610100291413621029 76786239393804640053943)
                  ·
                    rfl

theorem cell22_672933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_672933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672933 prefixEnd_672933 := by exact prefixLift 672933
  have htrace : WordTrace (prefixWord ++ tailWord_672933) baseStart_672933 baseEnd_672933 := by
    simpa [prefixWord, tailWord_672933, baseEnd_672933] using wordTrace_append hprefix tailTrace_672933
  have hstable : (prefixWord ++ tailWord_672933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672933).length < 2 ^ (prefixWord ++ tailWord_672933).sum := by decide
  have hdescent : baseEnd_672933 < baseStart_672933 := by decide
  rcases family_descends (prefixWord ++ tailWord_672933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_672946 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_672946 : Nat := 118140960795 + 672946 * 2 ^ 59
def prefixEnd_672946 : Nat := 4983230072969 + 3 ^ 40 * 672946 * 2
def baseEnd_672946 : Nat := 230363168347086219586789

theorem tailTrace_672946 : CollatzResearch.WordTrace tailWord_672946 prefixEnd_672946 230363168347086219586789 := by
  unfold tailWord_672946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136089255009761717965673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16362904680026031247908461 6136089255009761717965673)
  ·
    refine ⟨4602066941257321288474255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6136089255009761717965673 4602066941257321288474255)
    ·
      refine ⟨6903100411885981932711383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4602066941257321288474255 6903100411885981932711383)
      ·
        refine ⟨10354650617828972899067075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6903100411885981932711383 10354650617828972899067075)
        ·
          refine ⟨15531975926743459348600613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10354650617828972899067075 15531975926743459348600613)
          ·
            refine ⟨2912245486264398627862615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15531975926743459348600613 2912245486264398627862615)
            ·
              refine ⟨4368368229396597941793923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2912245486264398627862615 4368368229396597941793923)
              ·
                refine ⟨6552552344094896912690885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4368368229396597941793923 6552552344094896912690885)
                ·
                  refine ⟨1228603564517793171129541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6552552344094896912690885 1228603564517793171129541)
                  ·
                    refine ⟨230363168347086219586789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1228603564517793171129541 230363168347086219586789)
                    ·
                      rfl

theorem cell22_672946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_672946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_672946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_672946 prefixEnd_672946 := by exact prefixLift 672946
  have htrace : WordTrace (prefixWord ++ tailWord_672946) baseStart_672946 baseEnd_672946 := by
    simpa [prefixWord, tailWord_672946, baseEnd_672946] using wordTrace_append hprefix tailTrace_672946
  have hstable : (prefixWord ++ tailWord_672946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_672946).length < 2 ^ (prefixWord ++ tailWord_672946).sum := by decide
  have hdescent : baseEnd_672946 < baseStart_672946 := by decide
  rcases family_descends (prefixWord ++ tailWord_672946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673006 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_673006 : Nat := 118140960795 + 673006 * 2 ^ 59
def prefixEnd_673006 : Nat := 4983230072969 + 3 ^ 40 * 673006 * 2
def baseEnd_673006 : Nat := 76794569191088687695535

theorem tailTrace_673006 : CollatzResearch.WordTrace tailWord_673006 prefixEnd_673006 76794569191088687695535 := by
  unfold tailWord_673006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3068318174977709639880859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16364363599881118079364581 3068318174977709639880859)
  ·
    refine ⟨4602477262466564459821289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3068318174977709639880859 4602477262466564459821289)
    ·
      refine ⟨3451857946849923344865967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4602477262466564459821289 3451857946849923344865967)
      ·
        refine ⟨5177786920274885017298951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3451857946849923344865967 5177786920274885017298951)
        ·
          refine ⟨7766680380412327525948427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177786920274885017298951 7766680380412327525948427)
          ·
            refine ⟨11650020570618491288922641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7766680380412327525948427 11650020570618491288922641)
            ·
              refine ⟨8737515427963868466691981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11650020570618491288922641 8737515427963868466691981)
              ·
                refine ⟨3276568285486450675009493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8737515427963868466691981 3276568285486450675009493)
                ·
                  refine ⟨76794569191088687695535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3276568285486450675009493 76794569191088687695535)
                  ·
                    rfl

theorem cell22_673006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_673006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673006 prefixEnd_673006 := by exact prefixLift 673006
  have htrace : WordTrace (prefixWord ++ tailWord_673006) baseStart_673006 baseEnd_673006 := by
    simpa [prefixWord, tailWord_673006, baseEnd_673006] using wordTrace_append hprefix tailTrace_673006
  have hstable : (prefixWord ++ tailWord_673006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673006).length < 2 ^ (prefixWord ++ tailWord_673006).sum := by decide
  have hdescent : baseEnd_673006 < baseStart_673006 := by decide
  rcases family_descends (prefixWord ++ tailWord_673006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673130 : List Nat := [3, 1, 3, 3, 2, 1, 2, 7]
def baseStart_673130 : Nat := 118140960795 + 673130 * 2 ^ 59
def prefixEnd_673130 : Nat := 4983230072969 + 3 ^ 40 * 673130 * 2
def baseEnd_673130 : Nat := 25602906145263452554025

theorem tailTrace_673130 : CollatzResearch.WordTrace tailWord_673130 prefixEnd_673130 25602906145263452554025 := by
  unfold tailWord_673130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137767012843111574140211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16367378700914964197707229 6137767012843111574140211)
  ·
    refine ⟨9206650519264667361210317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6137767012843111574140211 9206650519264667361210317)
    ·
      refine ⟨3452493944724250260453869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9206650519264667361210317 3452493944724250260453869)
      ·
        refine ⟨1294685229271593847670201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3452493944724250260453869 1294685229271593847670201)
        ·
          refine ⟨971013921953695385752651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294685229271593847670201 971013921953695385752651)
          ·
            refine ⟨1456520882930543078628977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971013921953695385752651 1456520882930543078628977)
            ·
              refine ⟨1092390662197907308971733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1456520882930543078628977 1092390662197907308971733)
              ·
                refine ⟨25602906145263452554025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1092390662197907308971733 25602906145263452554025)
                ·
                  rfl

theorem cell22_673130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_673130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673130 prefixEnd_673130 := by exact prefixLift 673130
  have htrace : WordTrace (prefixWord ++ tailWord_673130) baseStart_673130 baseEnd_673130 := by
    simpa [prefixWord, tailWord_673130, baseEnd_673130] using wordTrace_append hprefix tailTrace_673130
  have hstable : (prefixWord ++ tailWord_673130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673130).length < 2 ^ (prefixWord ++ tailWord_673130).sum := by decide
  have hdescent : baseEnd_673130 < baseStart_673130 := by decide
  rcases family_descends (prefixWord ++ tailWord_673130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673134 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_673134 : Nat := 118140960795 + 673134 * 2 ^ 59
def prefixEnd_673134 : Nat := 4983230072969 + 3 ^ 40 * 673134 * 2
def baseEnd_673134 : Nat := 230427524589116395886213

theorem tailTrace_673134 : CollatzResearch.WordTrace tailWord_673134 prefixEnd_673134 230427524589116395886213 := by
  unfold tailWord_673134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3068901742919744372463307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16367475962238636653137637 3068901742919744372463307)
  ·
    refine ⟨4603352614379616558694961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3068901742919744372463307 4603352614379616558694961)
    ·
      refine ⟨3452514460784712419021221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4603352614379616558694961 3452514460784712419021221)
      ·
        refine ⟨647346461397133578566479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3452514460784712419021221 647346461397133578566479)
        ·
          refine ⟨971019692095700367849719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647346461397133578566479 971019692095700367849719)
          ·
            refine ⟨1456529538143550551774579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971019692095700367849719 1456529538143550551774579)
            ·
              refine ⟨2184794307215325827661869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456529538143550551774579 2184794307215325827661869)
              ·
                refine ⟨819297865205747185373201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184794307215325827661869 819297865205747185373201)
                ·
                  refine ⟨614473398904310389029901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 819297865205747185373201 614473398904310389029901)
                  ·
                    refine ⟨230427524589116395886213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 614473398904310389029901 230427524589116395886213)
                    ·
                      rfl

theorem cell22_673134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_673134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673134 prefixEnd_673134 := by exact prefixLift 673134
  have htrace : WordTrace (prefixWord ++ tailWord_673134) baseStart_673134 baseEnd_673134 := by
    simpa [prefixWord, tailWord_673134, baseEnd_673134] using wordTrace_append hprefix tailTrace_673134
  have hstable : (prefixWord ++ tailWord_673134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673134).length < 2 ^ (prefixWord ++ tailWord_673134).sum := by decide
  have hdescent : baseEnd_673134 < baseStart_673134 := by decide
  rcases family_descends (prefixWord ++ tailWord_673134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673205 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_673205 : Nat := 118140960795 + 673205 * 2 ^ 59
def prefixEnd_673205 : Nat := 4983230072969 + 3 ^ 40 * 673205 * 2
def baseEnd_673205 : Nat := 230451829340095877360995

theorem tailTrace_673205 : CollatzResearch.WordTrace tailWord_673205 prefixEnd_673205 230451829340095877360995 := by
  unfold tailWord_673205
  simp only [CollatzResearch.WordTrace]
  refine ⟨24553803526100734105541069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16369202350733822737027379 24553803526100734105541069)
  ·
    refine ⟨9207676322287775289577901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24553803526100734105541069 9207676322287775289577901)
    ·
      refine ⟨3452878620857915733591713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9207676322287775289577901 3452878620857915733591713)
      ·
        refine ⟨2589658965643436800193785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3452878620857915733591713 2589658965643436800193785)
        ·
          refine ⟨1942244224232577600145339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2589658965643436800193785 1942244224232577600145339)
          ·
            refine ⟨2913366336348866400218009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942244224232577600145339 2913366336348866400218009)
            ·
              refine ⟨2185024752261649800163507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2913366336348866400218009 2185024752261649800163507)
              ·
                refine ⟨3277537128392474700245261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185024752261649800163507 3277537128392474700245261)
                ·
                  refine ⟨1229076423147178012591973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3277537128392474700245261 1229076423147178012591973)
                  ·
                    refine ⟨230451829340095877360995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1229076423147178012591973 230451829340095877360995)
                    ·
                      rfl

theorem cell22_673205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_673205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673205 prefixEnd_673205 := by exact prefixLift 673205
  have htrace : WordTrace (prefixWord ++ tailWord_673205) baseStart_673205 baseEnd_673205 := by
    simpa [prefixWord, tailWord_673205, baseEnd_673205] using wordTrace_append hprefix tailTrace_673205
  have hstable : (prefixWord ++ tailWord_673205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673205).length < 2 ^ (prefixWord ++ tailWord_673205).sum := by decide
  have hdescent : baseEnd_673205 < baseStart_673205 := by decide
  rcases family_descends (prefixWord ++ tailWord_673205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673265 : List Nat := [1, 2, 2, 2, 3, 2, 4, 6]
def baseStart_673265 : Nat := 118140960795 + 673265 * 2 ^ 59
def prefixEnd_673265 : Nat := 4983230072969 + 3 ^ 40 * 673265 * 2
def baseEnd_673265 : Nat := 25608040951808413428979

theorem tailTrace_673265 : CollatzResearch.WordTrace tailWord_673265 prefixEnd_673265 25608040951808413428979 := by
  unfold tailWord_673265
  simp only [CollatzResearch.WordTrace]
  refine ⟨24555991905883364352725249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16370661270588909568483499 24555991905883364352725249)
  ·
    refine ⟨18416993929412523264543937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24555991905883364352725249 18416993929412523264543937)
    ·
      refine ⟨13812745447059392448407953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18416993929412523264543937 13812745447059392448407953)
      ·
        refine ⟨10359559085294544336305965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13812745447059392448407953 10359559085294544336305965)
        ·
          refine ⟨3884834656985454126114737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10359559085294544336305965 3884834656985454126114737)
          ·
            refine ⟨2913625992739090594586053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3884834656985454126114737 2913625992739090594586053)
            ·
              refine ⟨546304873638579486484885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2913625992739090594586053 546304873638579486484885)
              ·
                refine ⟨25608040951808413428979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 546304873638579486484885 25608040951808413428979)
                ·
                  rfl

theorem cell22_673265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 6].length) (baseStart_673265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673265 prefixEnd_673265 := by exact prefixLift 673265
  have htrace : WordTrace (prefixWord ++ tailWord_673265) baseStart_673265 baseEnd_673265 := by
    simpa [prefixWord, tailWord_673265, baseEnd_673265] using wordTrace_append hprefix tailTrace_673265
  have hstable : (prefixWord ++ tailWord_673265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673265).length < 2 ^ (prefixWord ++ tailWord_673265).sum := by decide
  have hdescent : baseEnd_673265 < baseStart_673265 := by decide
  rcases family_descends (prefixWord ++ tailWord_673265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673282 : List Nat := [3, 4, 1, 2, 1, 3, 8]
def baseStart_673282 : Nat := 118140960795 + 673282 * 2 ^ 59
def prefixEnd_673282 : Nat := 4983230072969 + 3 ^ 40 * 673282 * 2
def baseEnd_673282 : Nat := 8536229185692346043917

theorem tailTrace_673282 : CollatzResearch.WordTrace tailWord_673282 prefixEnd_673282 8536229185692346043917 := by
  unfold tailWord_673282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139152986705444064023525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16371074631214517504062733 6139152986705444064023525)
  ·
    refine ⟨1151091185007270762004411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6139152986705444064023525 1151091185007270762004411)
    ·
      refine ⟨1726636777510906143006617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151091185007270762004411 1726636777510906143006617)
      ·
        refine ⟨1294977583133179607254963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1726636777510906143006617 1294977583133179607254963)
        ·
          refine ⟨1942466374699769410882445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294977583133179607254963 1942466374699769410882445)
          ·
            refine ⟨728424890512413529080917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1942466374699769410882445 728424890512413529080917)
            ·
              refine ⟨8536229185692346043917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 728424890512413529080917 8536229185692346043917)
              ·
                rfl

theorem cell22_673282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 8].length) (baseStart_673282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673282 prefixEnd_673282 := by exact prefixLift 673282
  have htrace : WordTrace (prefixWord ++ tailWord_673282) baseStart_673282 baseEnd_673282 := by
    simpa [prefixWord, tailWord_673282, baseEnd_673282] using wordTrace_append hprefix tailTrace_673282
  have hstable : (prefixWord ++ tailWord_673282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673282).length < 2 ^ (prefixWord ++ tailWord_673282).sum := by decide
  have hdescent : baseEnd_673282 < baseStart_673282 := by decide
  rcases family_descends (prefixWord ++ tailWord_673282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673372 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 6]
def baseStart_673372 : Nat := 118140960795 + 673372 * 2 ^ 59
def prefixEnd_673372 : Nat := 4983230072969 + 3 ^ 40 * 673372 * 2
def baseEnd_673372 : Nat := 76836332284321036145161

theorem tailTrace_673372 : CollatzResearch.WordTrace tailWord_673372 prefixEnd_673372 76836332284321036145161 := by
  unfold tailWord_673372
  simp only [CollatzResearch.WordTrace]
  refine ⟨12279947258247860813435185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16373263010997147751246913 12279947258247860813435185)
  ·
    refine ⟨9209960443685895610076389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12279947258247860813435185 9209960443685895610076389)
    ·
      refine ⟨1726867583191105426889323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9209960443685895610076389 1726867583191105426889323)
      ·
        refine ⟨2590301374786658140333985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726867583191105426889323 2590301374786658140333985)
        ·
          refine ⟨1942726031089993605250489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2590301374786658140333985 1942726031089993605250489)
          ·
            refine ⟨1457044523317495203937867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1942726031089993605250489 1457044523317495203937867)
            ·
              refine ⟨2185566784976242805906801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457044523317495203937867 2185566784976242805906801)
              ·
                refine ⟨1639175088732182104430101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2185566784976242805906801 1639175088732182104430101)
                ·
                  refine ⟨76836332284321036145161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1639175088732182104430101 76836332284321036145161)
                  ·
                    rfl

theorem cell22_673372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_673372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673372 prefixEnd_673372 := by exact prefixLift 673372
  have htrace : WordTrace (prefixWord ++ tailWord_673372) baseStart_673372 baseEnd_673372 := by
    simpa [prefixWord, tailWord_673372, baseEnd_673372] using wordTrace_append hprefix tailTrace_673372
  have hstable : (prefixWord ++ tailWord_673372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673372).length < 2 ^ (prefixWord ++ tailWord_673372).sum := by decide
  have hdescent : baseEnd_673372 < baseStart_673372 := by decide
  rcases family_descends (prefixWord ++ tailWord_673372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673445 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 7]
def baseStart_673445 : Nat := 118140960795 + 673445 * 2 ^ 59
def prefixEnd_673445 : Nat := 4983230072969 + 3 ^ 40 * 673445 * 2
def baseEnd_673445 : Nat := 76844662081605083786753

theorem tailTrace_673445 : CollatzResearch.WordTrace tailWord_673445 prefixEnd_673445 76844662081605083786753 := by
  unfold tailWord_673445
  simp only [CollatzResearch.WordTrace]
  refine ⟨24562557045231255094277789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16375038030154170062851859 24562557045231255094277789)
  ·
    refine ⟨9210958891961720660354171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24562557045231255094277789 9210958891961720660354171)
    ·
      refine ⟨13816438337942580990531257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9210958891961720660354171 13816438337942580990531257)
      ·
        refine ⟨10362328753456935742898443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13816438337942580990531257 10362328753456935742898443)
        ·
          refine ⟨15543493130185403614347665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10362328753456935742898443 15543493130185403614347665)
          ·
            refine ⟨11657619847639052710760749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15543493130185403614347665 11657619847639052710760749)
            ·
              refine ⟨4371607442864644766535281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11657619847639052710760749 4371607442864644766535281)
              ·
                refine ⟨3278705582148483574901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371607442864644766535281 3278705582148483574901461)
                ·
                  refine ⟨76844662081605083786753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3278705582148483574901461 76844662081605083786753)
                  ·
                    rfl

theorem cell22_673445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_673445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673445 prefixEnd_673445 := by exact prefixLift 673445
  have htrace : WordTrace (prefixWord ++ tailWord_673445) baseStart_673445 baseEnd_673445 := by
    simpa [prefixWord, tailWord_673445, baseEnd_673445] using wordTrace_append hprefix tailTrace_673445
  have hstable : (prefixWord ++ tailWord_673445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673445).length < 2 ^ (prefixWord ++ tailWord_673445).sum := by decide
  have hdescent : baseEnd_673445 < baseStart_673445 := by decide
  rcases family_descends (prefixWord ++ tailWord_673445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673522 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_673522 : Nat := 118140960795 + 673522 * 2 ^ 59
def prefixEnd_673522 : Nat := 4983230072969 + 3 ^ 40 * 673522 * 2
def baseEnd_673522 : Nat := 230560344918412717185023

theorem tailTrace_673522 : CollatzResearch.WordTrace tailWord_673522 prefixEnd_673522 230560344918412717185023 := by
  unfold tailWord_673522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141341366488074311207705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16376910310634864829887213 6141341366488074311207705)
  ·
    refine ⟨4606006024866055733405779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6141341366488074311207705 4606006024866055733405779)
    ·
      refine ⟨6909009037299083600108669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606006024866055733405779 6909009037299083600108669)
      ·
        refine ⟨2590878388987156350040751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6909009037299083600108669 2590878388987156350040751)
        ·
          refine ⟨3886317583480734525061127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590878388987156350040751 3886317583480734525061127)
          ·
            refine ⟨5829476375221101787591691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3886317583480734525061127 5829476375221101787591691)
            ·
              refine ⟨8744214562831652681387537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5829476375221101787591691 8744214562831652681387537)
              ·
                refine ⟨6558160922123739511040653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8744214562831652681387537 6558160922123739511040653)
                ·
                  refine ⟨2459310345796402316640245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6558160922123739511040653 2459310345796402316640245)
                  ·
                    refine ⟨230560344918412717185023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2459310345796402316640245 230560344918412717185023)
                    ·
                      rfl

theorem cell22_673522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_673522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673522 prefixEnd_673522 := by exact prefixLift 673522
  have htrace : WordTrace (prefixWord ++ tailWord_673522) baseStart_673522 baseEnd_673522 := by
    simpa [prefixWord, tailWord_673522, baseEnd_673522] using wordTrace_append hprefix tailTrace_673522
  have hstable : (prefixWord ++ tailWord_673522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673522).length < 2 ^ (prefixWord ++ tailWord_673522).sum := by decide
  have hdescent : baseEnd_673522 < baseStart_673522 := by decide
  rcases family_descends (prefixWord ++ tailWord_673522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673537 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_673537 : Nat := 118140960795 + 673537 * 2 ^ 59
def prefixEnd_673537 : Nat := 4983230072969 + 3 ^ 40 * 673537 * 2
def baseEnd_673537 : Nat := 230565479724957678059977

theorem tailTrace_673537 : CollatzResearch.WordTrace tailWord_673537 prefixEnd_673537 230565479724957678059977 := by
  unfold tailWord_673537
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565912560897954806626865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16377275040598636537751243 24565912560897954806626865)
  ·
    refine ⟨18424434420673466104970149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24565912560897954806626865 18424434420673466104970149)
    ·
      refine ⟨3454581453876274894681903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18424434420673466104970149 3454581453876274894681903)
      ·
        refine ⟨5181872180814412342022855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3454581453876274894681903 5181872180814412342022855)
        ·
          refine ⟨7772808271221618513034283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181872180814412342022855 7772808271221618513034283)
          ·
            refine ⟨11659212406832427769551425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7772808271221618513034283 11659212406832427769551425)
            ·
              refine ⟨8744409305124320827163569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11659212406832427769551425 8744409305124320827163569)
              ·
                refine ⟨6558306978843240620372677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8744409305124320827163569 6558306978843240620372677)
                ·
                  refine ⟨1229682558533107616319877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6558306978843240620372677 1229682558533107616319877)
                  ·
                    refine ⟨230565479724957678059977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1229682558533107616319877 230565479724957678059977)
                    ·
                      rfl

theorem cell22_673537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_673537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673537 prefixEnd_673537 := by exact prefixLift 673537
  have htrace : WordTrace (prefixWord ++ tailWord_673537) baseStart_673537 baseEnd_673537 := by
    simpa [prefixWord, tailWord_673537, baseEnd_673537] using wordTrace_append hprefix tailTrace_673537
  have hstable : (prefixWord ++ tailWord_673537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673537).length < 2 ^ (prefixWord ++ tailWord_673537).sum := by decide
  have hdescent : baseEnd_673537 < baseStart_673537 := by decide
  rcases family_descends (prefixWord ++ tailWord_673537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673539 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 2, 3]
def baseStart_673539 : Nat := 118140960795 + 673539 * 2 ^ 59
def prefixEnd_673539 : Nat := 4983230072969 + 3 ^ 40 * 673539 * 2
def baseEnd_673539 : Nat := 230566164365830339509971

theorem tailTrace_673539 : CollatzResearch.WordTrace tailWord_673539 prefixEnd_673539 230566164365830339509971 := by
  unfold tailWord_673539
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565985506890709148199671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16377323671260472765466447 24565985506890709148199671)
  ·
    refine ⟨36848978260336063722299507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24565985506890709148199671 36848978260336063722299507)
    ·
      refine ⟨55273467390504095583449261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36848978260336063722299507 55273467390504095583449261)
      ·
        refine ⟨20727550271439035843793473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55273467390504095583449261 20727550271439035843793473)
        ·
          refine ⟨15545662703579276882845105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20727550271439035843793473 15545662703579276882845105)
          ·
            refine ⟨11659247027684457662133829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15545662703579276882845105 11659247027684457662133829)
            ·
              refine ⟨2186108817690835811650093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11659247027684457662133829 2186108817690835811650093)
              ·
                refine ⟨819790806634063429368785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2186108817690835811650093 819790806634063429368785)
                ·
                  refine ⟨614843104975547572026589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 819790806634063429368785 614843104975547572026589)
                  ·
                    refine ⟨230566164365830339509971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 614843104975547572026589 230566164365830339509971)
                    ·
                      rfl

theorem cell22_673539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 3].length) (baseStart_673539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673539 prefixEnd_673539 := by exact prefixLift 673539
  have htrace : WordTrace (prefixWord ++ tailWord_673539) baseStart_673539 baseEnd_673539 := by
    simpa [prefixWord, tailWord_673539, baseEnd_673539] using wordTrace_append hprefix tailTrace_673539
  have hstable : (prefixWord ++ tailWord_673539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673539).length < 2 ^ (prefixWord ++ tailWord_673539).sum := by decide
  have hdescent : baseEnd_673539 < baseStart_673539 := by decide
  rcases family_descends (prefixWord ++ tailWord_673539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673590 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_673590 : Nat := 118140960795 + 673590 * 2 ^ 59
def prefixEnd_673590 : Nat := 4983230072969 + 3 ^ 40 * 673590 * 2
def baseEnd_673590 : Nat := 230583622708083206484815

theorem tailTrace_673590 : CollatzResearch.WordTrace tailWord_673590 prefixEnd_673590 230583622708083206484815 := by
  unfold tailWord_673590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535490351856621553644139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16378563753137296572204149 1535490351856621553644139)
  ·
    refine ⟨2303235527784932330466209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1535490351856621553644139 2303235527784932330466209)
    ·
      refine ⟨1727426645838699247849657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2303235527784932330466209 1727426645838699247849657)
      ·
        refine ⟨1295569984379024435887243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1727426645838699247849657 1295569984379024435887243)
        ·
          refine ⟨1943354976568536653830865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295569984379024435887243 1943354976568536653830865)
          ·
            refine ⟨1457516232426402490373149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1943354976568536653830865 1457516232426402490373149)
            ·
              refine ⟨546568587159900933889931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1457516232426402490373149 546568587159900933889931)
              ·
                refine ⟨819852880739851400834897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546568587159900933889931 819852880739851400834897)
                ·
                  refine ⟨614889660554888550626173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 819852880739851400834897 614889660554888550626173)
                  ·
                    refine ⟨230583622708083206484815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 614889660554888550626173 230583622708083206484815)
                    ·
                      rfl

theorem cell22_673590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_673590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673590 prefixEnd_673590 := by exact prefixLift 673590
  have htrace : WordTrace (prefixWord ++ tailWord_673590) baseStart_673590 baseEnd_673590 := by
    simpa [prefixWord, tailWord_673590, baseEnd_673590] using wordTrace_append hprefix tailTrace_673590
  have hstable : (prefixWord ++ tailWord_673590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673590).length < 2 ^ (prefixWord ++ tailWord_673590).sum := by decide
  have hdescent : baseEnd_673590 < baseStart_673590 := by decide
  rcases family_descends (prefixWord ++ tailWord_673590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673618 : List Nat := [3, 2, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_673618 : Nat := 118140960795 + 673618 * 2 ^ 59
def prefixEnd_673618 : Nat := 4983230072969 + 3 ^ 40 * 673618 * 2
def baseEnd_673618 : Nat := 230593207680300466784729

theorem tailTrace_673618 : CollatzResearch.WordTrace tailWord_673618 prefixEnd_673618 230593207680300466784729 := by
  unfold tailWord_673618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6142216718401126410081377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16379244582403003760217005 6142216718401126410081377)
  ·
    refine ⟨4606662538800844807561033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6142216718401126410081377 4606662538800844807561033)
    ·
      refine ⟨3454996904100633605670775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4606662538800844807561033 3454996904100633605670775)
      ·
        refine ⟨5182495356150950408506163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3454996904100633605670775 5182495356150950408506163)
        ·
          refine ⟨7773743034226425612759245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182495356150950408506163 7773743034226425612759245)
          ·
            refine ⟨2915153637834909604784717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7773743034226425612759245 2915153637834909604784717)
            ·
              refine ⟨1093182614188091101794269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2915153637834909604784717 1093182614188091101794269)
              ·
                refine ⟨409943480320534163172851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1093182614188091101794269 409943480320534163172851)
                ·
                  refine ⟨614915220480801244759277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409943480320534163172851 614915220480801244759277)
                  ·
                    refine ⟨230593207680300466784729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 614915220480801244759277 230593207680300466784729)
                    ·
                      rfl

theorem cell22_673618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_673618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673618 prefixEnd_673618 := by exact prefixLift 673618
  have htrace : WordTrace (prefixWord ++ tailWord_673618) baseStart_673618 baseEnd_673618 := by
    simpa [prefixWord, tailWord_673618, baseEnd_673618] using wordTrace_append hprefix tailTrace_673618
  have hstable : (prefixWord ++ tailWord_673618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673618).length < 2 ^ (prefixWord ++ tailWord_673618).sum := by decide
  have hdescent : baseEnd_673618 < baseStart_673618 := by decide
  rcases family_descends (prefixWord ++ tailWord_673618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673635 : List Nat := [1, 1, 1, 5, 4, 1, 3, 2, 1, 3]
def baseStart_673635 : Nat := 118140960795 + 673635 * 2 ^ 59
def prefixEnd_673635 : Nat := 4983230072969 + 3 ^ 40 * 673635 * 2
def baseEnd_673635 : Nat := 230599027127718089109677

theorem tailTrace_673635 : CollatzResearch.WordTrace tailWord_673635 prefixEnd_673635 230599027127718089109677 := by
  unfold tailWord_673635
  simp only [CollatzResearch.WordTrace]
  refine ⟨24569486914542917543694359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16379657943028611695796239 24569486914542917543694359)
  ·
    refine ⟨36854230371814376315541539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24569486914542917543694359 36854230371814376315541539)
    ·
      refine ⟨55281345557721564473312309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36854230371814376315541539 55281345557721564473312309)
      ·
        refine ⟨5182626146036396669373029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55281345557721564473312309 5182626146036396669373029)
        ·
          refine ⟨971742402381824375507443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5182626146036396669373029 971742402381824375507443)
          ·
            refine ⟨1457613603572736563261165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971742402381824375507443 1457613603572736563261165)
            ·
              refine ⟨546605101339776211222937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1457613603572736563261165 546605101339776211222937)
              ·
                refine ⟨409953826004832158417203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546605101339776211222937 409953826004832158417203)
                ·
                  refine ⟨614930739007248237625805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409953826004832158417203 614930739007248237625805)
                  ·
                    refine ⟨230599027127718089109677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 614930739007248237625805 230599027127718089109677)
                    ·
                      rfl

theorem cell22_673635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 3].length) (baseStart_673635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673635 prefixEnd_673635 := by exact prefixLift 673635
  have htrace : WordTrace (prefixWord ++ tailWord_673635) baseStart_673635 baseEnd_673635 := by
    simpa [prefixWord, tailWord_673635, baseEnd_673635] using wordTrace_append hprefix tailTrace_673635
  have hstable : (prefixWord ++ tailWord_673635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673635).length < 2 ^ (prefixWord ++ tailWord_673635).sum := by decide
  have hdescent : baseEnd_673635 < baseStart_673635 := by decide
  rcases family_descends (prefixWord ++ tailWord_673635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673686 : List Nat := [5, 3, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_673686 : Nat := 118140960795 + 673686 * 2 ^ 59
def prefixEnd_673686 : Nat := 4983230072969 + 3 ^ 40 * 673686 * 2
def baseEnd_673686 : Nat := 230616485469970956084521

theorem tailTrace_673686 : CollatzResearch.WordTrace tailWord_673686 prefixEnd_673686 230616485469970956084521 := by
  unfold tailWord_673686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535709189834884578362557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16380898024905435502533941 1535709189834884578362557)
  ·
    refine ⟨575890946188081716885959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1535709189834884578362557 575890946188081716885959)
    ·
      refine ⟨863836419282122575328939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575890946188081716885959 863836419282122575328939)
      ·
        refine ⟨1295754628923183862993409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863836419282122575328939 1295754628923183862993409)
        ·
          refine ⟨971815971692387897245057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1295754628923183862993409 971815971692387897245057)
          ·
            refine ⟨728861978769290922933793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 971815971692387897245057 728861978769290922933793)
            ·
              refine ⟨546646484076968192200345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728861978769290922933793 546646484076968192200345)
              ·
                refine ⟨409984863057726144150259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546646484076968192200345 409984863057726144150259)
                ·
                  refine ⟨614977294586589216225389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 409984863057726144150259 614977294586589216225389)
                  ·
                    refine ⟨230616485469970956084521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 614977294586589216225389 230616485469970956084521)
                    ·
                      rfl

theorem cell22_673686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_673686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673686 prefixEnd_673686 := by exact prefixLift 673686
  have htrace : WordTrace (prefixWord ++ tailWord_673686) baseStart_673686 baseEnd_673686 := by
    simpa [prefixWord, tailWord_673686, baseEnd_673686] using wordTrace_append hprefix tailTrace_673686
  have hstable : (prefixWord ++ tailWord_673686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673686).length < 2 ^ (prefixWord ++ tailWord_673686).sum := by decide
  have hdescent : baseEnd_673686 < baseStart_673686 := by decide
  rcases family_descends (prefixWord ++ tailWord_673686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673687 : List Nat := [1, 1, 3, 3, 1, 13]
def baseStart_673687 : Nat := 118140960795 + 673687 * 2 ^ 59
def prefixEnd_673687 : Nat := 4983230072969 + 3 ^ 40 * 673687 * 2
def baseEnd_673687 : Nat := 2847121330745768972957

theorem tailTrace_673687 : CollatzResearch.WordTrace tailWord_673687 prefixEnd_673687 2847121330745768972957 := by
  unfold tailWord_673687
  simp only [CollatzResearch.WordTrace]
  refine ⟨24571383510354530424587315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16380922340236353616391543 24571383510354530424587315)
  ·
    refine ⟨36857075265531795636880973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24571383510354530424587315 36857075265531795636880973)
    ·
      refine ⟨13821403224574423363830365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36857075265531795636880973 13821403224574423363830365)
      ·
        refine ⟨5183026209215408761436387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13821403224574423363830365 5183026209215408761436387)
        ·
          refine ⟨7774539313823113142154581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5183026209215408761436387 7774539313823113142154581)
          ·
            refine ⟨2847121330745768972957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 7774539313823113142154581 2847121330745768972957)
            ·
              rfl

theorem cell22_673687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 13].length) (baseStart_673687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673687 prefixEnd_673687 := by exact prefixLift 673687
  have htrace : WordTrace (prefixWord ++ tailWord_673687) baseStart_673687 baseEnd_673687 := by
    simpa [prefixWord, tailWord_673687, baseEnd_673687] using wordTrace_append hprefix tailTrace_673687
  have hstable : (prefixWord ++ tailWord_673687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673687).length < 2 ^ (prefixWord ++ tailWord_673687).sum := by decide
  have hdescent : baseEnd_673687 < baseStart_673687 := by decide
  rcases family_descends (prefixWord ++ tailWord_673687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673689 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_673689 : Nat := 118140960795 + 673689 * 2 ^ 59
def prefixEnd_673689 : Nat := 4983230072969 + 3 ^ 40 * 673689 * 2
def baseEnd_673689 : Nat := 230617512431279948259511

theorem tailTrace_673689 : CollatzResearch.WordTrace tailWord_673689 prefixEnd_673689 230617512431279948259511 := by
  unfold tailWord_673689
  simp only [CollatzResearch.WordTrace]
  refine ⟨24571456456347284766160121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16380970970898189844106747 24571456456347284766160121)
  ·
    refine ⟨18428592342260463574620091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24571456456347284766160121 18428592342260463574620091)
    ·
      refine ⟨27642888513390695361930137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18428592342260463574620091 27642888513390695361930137)
      ·
        refine ⟨20732166385043021521447603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27642888513390695361930137 20732166385043021521447603)
        ·
          refine ⟨31098249577564532282171405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20732166385043021521447603 31098249577564532282171405)
          ·
            refine ⟨11661843591586699605814277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31098249577564532282171405 11661843591586699605814277)
            ·
              refine ⟨2186595673422506176090177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11661843591586699605814277 2186595673422506176090177)
              ·
                refine ⟨1639946755066879632067633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186595673422506176090177 1639946755066879632067633)
                ·
                  refine ⟨1229960066300159724050725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639946755066879632067633 1229960066300159724050725)
                  ·
                    refine ⟨230617512431279948259511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1229960066300159724050725 230617512431279948259511)
                    ·
                      rfl

theorem cell22_673689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_673689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673689 prefixEnd_673689 := by exact prefixLift 673689
  have htrace : WordTrace (prefixWord ++ tailWord_673689) baseStart_673689 baseEnd_673689 := by
    simpa [prefixWord, tailWord_673689, baseEnd_673689] using wordTrace_append hprefix tailTrace_673689
  have hstable : (prefixWord ++ tailWord_673689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673689).length < 2 ^ (prefixWord ++ tailWord_673689).sum := by decide
  have hdescent : baseEnd_673689 < baseStart_673689 := by decide
  rcases family_descends (prefixWord ++ tailWord_673689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673693 : List Nat := [1, 4, 2, 1, 2, 2, 4, 2, 4]
def baseStart_673693 : Nat := 118140960795 + 673693 * 2 ^ 59
def prefixEnd_673693 : Nat := 4983230072969 + 3 ^ 40 * 673693 * 2
def baseEnd_673693 : Nat := 76872960571008423719833

theorem tailTrace_673693 : CollatzResearch.WordTrace tailWord_673693 prefixEnd_673693 76872960571008423719833 := by
  unfold tailWord_673693
  simp only [CollatzResearch.WordTrace]
  refine ⟨24571602348332793449305733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16381068232221862299537155 24571602348332793449305733)
  ·
    refine ⟨4607175440312398771744825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24571602348332793449305733 4607175440312398771744825)
    ·
      refine ⟨3455381580234299078808619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4607175440312398771744825 3455381580234299078808619)
      ·
        refine ⟨5183072370351448618212929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3455381580234299078808619 5183072370351448618212929)
        ·
          refine ⟨3887304277763586463659697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5183072370351448618212929 3887304277763586463659697)
          ·
            refine ⟨2915478208322689847744773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3887304277763586463659697 2915478208322689847744773)
            ·
              refine ⟨546652164060504346452145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2915478208322689847744773 546652164060504346452145)
              ·
                refine ⟨409989123045378259839109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546652164060504346452145 409989123045378259839109)
                ·
                  refine ⟨76872960571008423719833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409989123045378259839109 76872960571008423719833)
                  ·
                    rfl

theorem cell22_673693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_673693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673693 prefixEnd_673693 := by exact prefixLift 673693
  have htrace : WordTrace (prefixWord ++ tailWord_673693) baseStart_673693 baseEnd_673693 := by
    simpa [prefixWord, tailWord_673693, baseEnd_673693] using wordTrace_append hprefix tailTrace_673693
  have hstable : (prefixWord ++ tailWord_673693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673693).length < 2 ^ (prefixWord ++ tailWord_673693).sum := by decide
  have hdescent : baseEnd_673693 < baseStart_673693 := by decide
  rcases family_descends (prefixWord ++ tailWord_673693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673710 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_673710 : Nat := 118140960795 + 673710 * 2 ^ 59
def prefixEnd_673710 : Nat := 4983230072969 + 3 ^ 40 * 673710 * 2
def baseEnd_673710 : Nat := 76874900386814297828149

theorem tailTrace_673710 : CollatzResearch.WordTrace tailWord_673710 prefixEnd_673710 76874900386814297828149 := by
  unfold tailWord_673710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071527798658900669084323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16381481592847470235116389 3071527798658900669084323)
  ·
    refine ⟨4607291697988351003626485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3071527798658900669084323 4607291697988351003626485)
    ·
      refine ⟨431933596686407906589983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4607291697988351003626485 431933596686407906589983)
      ·
        refine ⟨647900395029611859884975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431933596686407906589983 647900395029611859884975)
        ·
          refine ⟨971850592544417789827463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647900395029611859884975 971850592544417789827463)
          ·
            refine ⟨1457775888816626684741195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971850592544417789827463 1457775888816626684741195)
            ·
              refine ⟨2186663833224940027111793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457775888816626684741195 2186663833224940027111793)
              ·
                refine ⟨1639997874918705020333845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186663833224940027111793 1639997874918705020333845)
                ·
                  refine ⟨76874900386814297828149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1639997874918705020333845 76874900386814297828149)
                  ·
                    rfl

theorem cell22_673710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_673710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673710 prefixEnd_673710 := by exact prefixLift 673710
  have htrace : WordTrace (prefixWord ++ tailWord_673710) baseStart_673710 baseEnd_673710 := by
    simpa [prefixWord, tailWord_673710, baseEnd_673710] using wordTrace_append hprefix tailTrace_673710
  have hstable : (prefixWord ++ tailWord_673710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673710).length < 2 ^ (prefixWord ++ tailWord_673710).sum := by decide
  have hdescent : baseEnd_673710 < baseStart_673710 := by decide
  rcases family_descends (prefixWord ++ tailWord_673710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673753 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 3, 3]
def baseStart_673753 : Nat := 118140960795 + 673753 * 2 ^ 59
def prefixEnd_673753 : Nat := 4983230072969 + 3 ^ 40 * 673753 * 2
def baseEnd_673753 : Nat := 230639420939205114659315

theorem tailTrace_673753 : CollatzResearch.WordTrace tailWord_673753 prefixEnd_673753 230639420939205114659315 := by
  unfold tailWord_673753
  simp only [CollatzResearch.WordTrace]
  refine ⟨24573790728115423696489913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16382527152076949130993275 24573790728115423696489913)
  ·
    refine ⟨18430343046086567772367435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24573790728115423696489913 18430343046086567772367435)
    ·
      refine ⟨27645514569129851658551153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18430343046086567772367435 27645514569129851658551153)
      ·
        refine ⟨20734135926847388743913365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27645514569129851658551153 20734135926847388743913365)
        ·
          refine ⟨971912621570971347370939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20734135926847388743913365 971912621570971347370939)
          ·
            refine ⟨1457868932356457021056409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971912621570971347370939 1457868932356457021056409)
            ·
              refine ⟨1093401699267342765792307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457868932356457021056409 1093401699267342765792307)
              ·
                refine ⟨1640102548901014148688461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093401699267342765792307 1640102548901014148688461)
                ·
                  refine ⟨615038455837880305758173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1640102548901014148688461 615038455837880305758173)
                  ·
                    refine ⟨230639420939205114659315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615038455837880305758173 230639420939205114659315)
                    ·
                      rfl

theorem cell22_673753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_673753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673753 prefixEnd_673753 := by exact prefixLift 673753
  have htrace : WordTrace (prefixWord ++ tailWord_673753) baseStart_673753 baseEnd_673753 := by
    simpa [prefixWord, tailWord_673753, baseEnd_673753] using wordTrace_append hprefix tailTrace_673753
  have hstable : (prefixWord ++ tailWord_673753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673753).length < 2 ^ (prefixWord ++ tailWord_673753).sum := by decide
  have hdescent : baseEnd_673753 < baseStart_673753 := by decide
  rcases family_descends (prefixWord ++ tailWord_673753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673764 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_673764 : Nat := 118140960795 + 673764 * 2 ^ 59
def prefixEnd_673764 : Nat := 4983230072969 + 3 ^ 40 * 673764 * 2
def baseEnd_673764 : Nat := 230643186464004752634281

theorem tailTrace_673764 : CollatzResearch.WordTrace tailWord_673764 prefixEnd_673764 230643186464004752634281 := by
  unfold tailWord_673764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12287095965537786287570173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16382794620717048383426897 12287095965537786287570173)
  ·
    refine ⟨4607660987076669857838815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12287095965537786287570173 4607660987076669857838815)
    ·
      refine ⟨6911491480615004786758223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4607660987076669857838815 6911491480615004786758223)
      ·
        refine ⟨10367237220922507180137335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6911491480615004786758223 10367237220922507180137335)
        ·
          refine ⟨15550855831383760770206003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10367237220922507180137335 15550855831383760770206003)
          ·
            refine ⟨23326283747075641155309005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15550855831383760770206003 23326283747075641155309005)
            ·
              refine ⟨8747356405153365433240877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23326283747075641155309005 8747356405153365433240877)
              ·
                refine ⟨3280258651932512037465329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8747356405153365433240877 3280258651932512037465329)
                ·
                  refine ⟨2460193988949384028098997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3280258651932512037465329 2460193988949384028098997)
                  ·
                    refine ⟨230643186464004752634281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2460193988949384028098997 230643186464004752634281)
                    ·
                      rfl

theorem cell22_673764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_673764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673764 prefixEnd_673764 := by exact prefixLift 673764
  have htrace : WordTrace (prefixWord ++ tailWord_673764) baseStart_673764 baseEnd_673764 := by
    simpa [prefixWord, tailWord_673764, baseEnd_673764] using wordTrace_append hprefix tailTrace_673764
  have hstable : (prefixWord ++ tailWord_673764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673764).length < 2 ^ (prefixWord ++ tailWord_673764).sum := by decide
  have hdescent : baseEnd_673764 < baseStart_673764 := by decide
  rcases family_descends (prefixWord ++ tailWord_673764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673779 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 3, 4]
def baseStart_673779 : Nat := 118140960795 + 673779 * 2 ^ 59
def prefixEnd_673779 : Nat := 4983230072969 + 3 ^ 40 * 673779 * 2
def baseEnd_673779 : Nat := 230648321270549713509235

theorem tailTrace_673779 : CollatzResearch.WordTrace tailWord_673779 prefixEnd_673779 230648321270549713509235 := by
  unfold tailWord_673779
  simp only [CollatzResearch.WordTrace]
  refine ⟨24574739026021230136936391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16383159350680820091290927 24574739026021230136936391)
  ·
    refine ⟨36862108539031845205404587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24574739026021230136936391 36862108539031845205404587)
    ·
      refine ⟨55293162808547767808106881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36862108539031845205404587 55293162808547767808106881)
      ·
        refine ⟨41469872106410825856080161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55293162808547767808106881 41469872106410825856080161)
        ·
          refine ⟨31102404079808119392060121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41469872106410825856080161 31102404079808119392060121)
          ·
            refine ⟨23326803059856089544045091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31102404079808119392060121 23326803059856089544045091)
            ·
              refine ⟨34990204589784134316067637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23326803059856089544045091 34990204589784134316067637)
              ·
                refine ⟨3280331680292262592131341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34990204589784134316067637 3280331680292262592131341)
                ·
                  refine ⟨1230124380109598472049253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3280331680292262592131341 1230124380109598472049253)
                  ·
                    refine ⟨230648321270549713509235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1230124380109598472049253 230648321270549713509235)
                    ·
                      rfl

theorem cell22_673779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 4].length) (baseStart_673779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673779 prefixEnd_673779 := by exact prefixLift 673779
  have htrace : WordTrace (prefixWord ++ tailWord_673779) baseStart_673779 baseEnd_673779 := by
    simpa [prefixWord, tailWord_673779, baseEnd_673779] using wordTrace_append hprefix tailTrace_673779
  have hstable : (prefixWord ++ tailWord_673779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673779).length < 2 ^ (prefixWord ++ tailWord_673779).sum := by decide
  have hdescent : baseEnd_673779 < baseStart_673779 := by decide
  rcases family_descends (prefixWord ++ tailWord_673779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673811 : List Nat := [1, 1, 1, 2, 1, 4, 2, 6, 4]
def baseStart_673811 : Nat := 118140960795 + 673811 * 2 ^ 59
def prefixEnd_673811 : Nat := 4983230072969 + 3 ^ 40 * 673811 * 2
def baseEnd_673811 : Nat := 76886425174837432236379

theorem tailTrace_673811 : CollatzResearch.WordTrace tailWord_673811 prefixEnd_673811 76886425174837432236379 := by
  unfold tailWord_673811
  simp only [CollatzResearch.WordTrace]
  refine ⟨24575906161905299602101287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16383937441270199734734191 24575906161905299602101287)
  ·
    refine ⟨36863859242857949403151931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24575906161905299602101287 36863859242857949403151931)
    ·
      refine ⟨55295788864286924104727897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36863859242857949403151931 55295788864286924104727897)
      ·
        refine ⟨41471841648215193078545923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55295788864286924104727897 41471841648215193078545923)
        ·
          refine ⟨62207762472322789617818885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41471841648215193078545923 62207762472322789617818885)
          ·
            refine ⟨11663955463560523053341041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62207762472322789617818885 11663955463560523053341041)
            ·
              refine ⟨8747966597670392290005781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11663955463560523053341041 8747966597670392290005781)
              ·
                refine ⟨410060934265799638594021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8747966597670392290005781 410060934265799638594021)
                ·
                  refine ⟨76886425174837432236379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410060934265799638594021 76886425174837432236379)
                  ·
                    rfl

theorem cell22_673811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 4].length) (baseStart_673811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673811 prefixEnd_673811 := by exact prefixLift 673811
  have htrace : WordTrace (prefixWord ++ tailWord_673811) baseStart_673811 baseEnd_673811 := by
    simpa [prefixWord, tailWord_673811, baseEnd_673811] using wordTrace_append hprefix tailTrace_673811
  have hstable : (prefixWord ++ tailWord_673811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673811).length < 2 ^ (prefixWord ++ tailWord_673811).sum := by decide
  have hdescent : baseEnd_673811 < baseStart_673811 := by decide
  rcases family_descends (prefixWord ++ tailWord_673811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673826 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_673826 : Nat := 118140960795 + 673826 * 2 ^ 59
def prefixEnd_673826 : Nat := 4983230072969 + 3 ^ 40 * 673826 * 2
def baseEnd_673826 : Nat := 230664410331057257584091

theorem tailTrace_673826 : CollatzResearch.WordTrace tailWord_673826 prefixEnd_673826 230664410331057257584091 := by
  unfold tailWord_673826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144113314212739290974333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16384302171233971442598221 6144113314212739290974333)
  ·
    refine ⟨2304042492829777234115375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6144113314212739290974333 2304042492829777234115375)
    ·
      refine ⟨3456063739244665851173063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304042492829777234115375 3456063739244665851173063)
      ·
        refine ⟨5184095608866998776759595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456063739244665851173063 5184095608866998776759595)
        ·
          refine ⟨7776143413300498165139393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184095608866998776759595 7776143413300498165139393)
          ·
            refine ⟨5832107559975373623854545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7776143413300498165139393 5832107559975373623854545)
            ·
              refine ⟨4374080669981530217890909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5832107559975373623854545 4374080669981530217890909)
              ·
                refine ⟨1640280251243073831709091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4374080669981530217890909 1640280251243073831709091)
                ·
                  refine ⟨2460420376864610747563637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1640280251243073831709091 2460420376864610747563637)
                  ·
                    refine ⟨230664410331057257584091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2460420376864610747563637 230664410331057257584091)
                    ·
                      rfl

theorem cell22_673826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_673826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673826 prefixEnd_673826 := by exact prefixLift 673826
  have htrace : WordTrace (prefixWord ++ tailWord_673826) baseStart_673826 baseEnd_673826 := by
    simpa [prefixWord, tailWord_673826, baseEnd_673826] using wordTrace_append hprefix tailTrace_673826
  have hstable : (prefixWord ++ tailWord_673826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673826).length < 2 ^ (prefixWord ++ tailWord_673826).sum := by decide
  have hdescent : baseEnd_673826 < baseStart_673826 := by decide
  rcases family_descends (prefixWord ++ tailWord_673826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673841 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_673841 : Nat := 118140960795 + 673841 * 2 ^ 59
def prefixEnd_673841 : Nat := 4983230072969 + 3 ^ 40 * 673841 * 2
def baseEnd_673841 : Nat := 230669545137602218459045

theorem tailTrace_673841 : CollatzResearch.WordTrace tailWord_673841 prefixEnd_673841 230669545137602218459045 := by
  unfold tailWord_673841
  simp only [CollatzResearch.WordTrace]
  refine ⟨24577000351796614725693377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16384666901197743150462251 24577000351796614725693377)
  ·
    refine ⟨18432750263847461044270033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24577000351796614725693377 18432750263847461044270033)
    ·
      refine ⟨13824562697885595783202525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18432750263847461044270033 13824562697885595783202525)
      ·
        refine ⟨5184211011707098418700947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13824562697885595783202525 5184211011707098418700947)
        ·
          refine ⟨7776316517560647628051421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184211011707098418700947 7776316517560647628051421)
          ·
            refine ⟨2916118694085242860519283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7776316517560647628051421 2916118694085242860519283)
            ·
              refine ⟨4374178041127864290778925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2916118694085242860519283 4374178041127864290778925)
              ·
                refine ⟨1640316765422949109042097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4374178041127864290778925 1640316765422949109042097)
                ·
                  refine ⟨1230237574067211831781573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1640316765422949109042097 1230237574067211831781573)
                  ·
                    refine ⟨230669545137602218459045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1230237574067211831781573 230669545137602218459045)
                    ·
                      rfl

theorem cell22_673841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_673841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673841 prefixEnd_673841 := by exact prefixLift 673841
  have htrace : WordTrace (prefixWord ++ tailWord_673841) baseStart_673841 baseEnd_673841 := by
    simpa [prefixWord, tailWord_673841, baseEnd_673841] using wordTrace_append hprefix tailTrace_673841
  have hstable : (prefixWord ++ tailWord_673841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673841).length < 2 ^ (prefixWord ++ tailWord_673841).sum := by decide
  have hdescent : baseEnd_673841 < baseStart_673841 := by decide
  rcases family_descends (prefixWord ++ tailWord_673841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673888 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 3, 3]
def baseStart_673888 : Nat := 118140960795 + 673888 * 2 ^ 59
def prefixEnd_673888 : Nat := 4983230072969 + 3 ^ 40 * 673888 * 2
def baseEnd_673888 : Nat := 230685634198109762533901

theorem tailTrace_673888 : CollatzResearch.WordTrace tailWord_673888 prefixEnd_673888 230685634198109762533901 := by
  unfold tailWord_673888
  simp only [CollatzResearch.WordTrace]
  refine ⟨12289357291313170876327159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16385809721750894501769545 12289357291313170876327159)
  ·
    refine ⟨18434035936969756314490739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12289357291313170876327159 18434035936969756314490739)
    ·
      refine ⟨27651053905454634471736109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18434035936969756314490739 27651053905454634471736109)
      ·
        refine ⟨10369145214545487926901041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27651053905454634471736109 10369145214545487926901041)
        ·
          refine ⟨7776858910909115945175781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10369145214545487926901041 7776858910909115945175781)
          ·
            refine ⟨1458161045795459239720459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7776858910909115945175781 1458161045795459239720459)
            ·
              refine ⟨2187241568693188859580689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458161045795459239720459 2187241568693188859580689)
              ·
                refine ⟨1640431176519891644685517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187241568693188859580689 1640431176519891644685517)
                ·
                  refine ⟨615161691194959366757069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1640431176519891644685517 615161691194959366757069)
                  ·
                    refine ⟨230685634198109762533901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615161691194959366757069 230685634198109762533901)
                    ·
                      rfl

theorem cell22_673888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_673888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673888 prefixEnd_673888 := by exact prefixLift 673888
  have htrace : WordTrace (prefixWord ++ tailWord_673888) baseStart_673888 baseEnd_673888 := by
    simpa [prefixWord, tailWord_673888, baseEnd_673888] using wordTrace_append hprefix tailTrace_673888
  have hstable : (prefixWord ++ tailWord_673888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673888).length < 2 ^ (prefixWord ++ tailWord_673888).sum := by decide
  have hdescent : baseEnd_673888 < baseStart_673888 := by decide
  rcases family_descends (prefixWord ++ tailWord_673888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673890 : List Nat := [3, 3, 2, 2, 2, 1, 3, 6]
def baseStart_673890 : Nat := 118140960795 + 673890 * 2 ^ 59
def prefixEnd_673890 : Nat := 4983230072969 + 3 ^ 40 * 673890 * 2
def baseEnd_673890 : Nat := 25631813204331380442655

theorem tailTrace_673890 : CollatzResearch.WordTrace tailWord_673890 prefixEnd_673890 25631813204331380442655 := by
  unfold tailWord_673890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144696882154774023556781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16385858352412730729484749 6144696882154774023556781)
  ·
    refine ⟨2304261330808040258833793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6144696882154774023556781 2304261330808040258833793)
    ·
      refine ⟨1728195998106030194125345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2304261330808040258833793 1728195998106030194125345)
      ·
        refine ⟨1296146998579522645594009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1728195998106030194125345 1296146998579522645594009)
        ·
          refine ⟨972110248934641984195507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296146998579522645594009 972110248934641984195507)
          ·
            refine ⟨1458165373401962976293261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972110248934641984195507 1458165373401962976293261)
            ·
              refine ⟨546812015025736116109973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1458165373401962976293261 546812015025736116109973)
              ·
                refine ⟨25631813204331380442655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 546812015025736116109973 25631813204331380442655)
                ·
                  rfl

theorem cell22_673890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_673890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673890 prefixEnd_673890 := by exact prefixLift 673890
  have htrace : WordTrace (prefixWord ++ tailWord_673890) baseStart_673890 baseEnd_673890 := by
    simpa [prefixWord, tailWord_673890, baseEnd_673890] using wordTrace_append hprefix tailTrace_673890
  have hstable : (prefixWord ++ tailWord_673890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673890).length < 2 ^ (prefixWord ++ tailWord_673890).sum := by decide
  have hdescent : baseEnd_673890 < baseStart_673890 := by decide
  rcases family_descends (prefixWord ++ tailWord_673890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_673901 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 7]
def baseStart_673901 : Nat := 118140960795 + 673901 * 2 ^ 59
def prefixEnd_673901 : Nat := 4983230072969 + 3 ^ 40 * 673901 * 2
def baseEnd_673901 : Nat := 76896694787927353986287

theorem tailTrace_673901 : CollatzResearch.WordTrace tailWord_673901 prefixEnd_673901 76896694787927353986287 := by
  unfold tailWord_673901
  simp only [CollatzResearch.WordTrace]
  refine ⟨24579188731579244972877557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16386125821052829981918371 24579188731579244972877557)
  ·
    refine ⟨2304298943585554216207271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24579188731579244972877557 2304298943585554216207271)
    ·
      refine ⟨3456448415378331324310907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304298943585554216207271 3456448415378331324310907)
      ·
        refine ⟨5184672623067496986466361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456448415378331324310907 5184672623067496986466361)
        ·
          refine ⟨3888504467300622739849771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5184672623067496986466361 3888504467300622739849771)
          ·
            refine ⟨5832756700950934109774657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888504467300622739849771 5832756700950934109774657)
            ·
              refine ⟨4374567525713200582330993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5832756700950934109774657 4374567525713200582330993)
              ·
                refine ⟨3280925644284900436748245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4374567525713200582330993 3280925644284900436748245)
                ·
                  refine ⟨76896694787927353986287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3280925644284900436748245 76896694787927353986287)
                  ·
                    rfl

theorem cell22_673901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_673901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_673901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_673901 prefixEnd_673901 := by exact prefixLift 673901
  have htrace : WordTrace (prefixWord ++ tailWord_673901) baseStart_673901 baseEnd_673901 := by
    simpa [prefixWord, tailWord_673901, baseEnd_673901] using wordTrace_append hprefix tailTrace_673901
  have hstable : (prefixWord ++ tailWord_673901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_673901).length < 2 ^ (prefixWord ++ tailWord_673901).sum := by decide
  have hdescent : baseEnd_673901 < baseStart_673901 := by decide
  rcases family_descends (prefixWord ++ tailWord_673901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
