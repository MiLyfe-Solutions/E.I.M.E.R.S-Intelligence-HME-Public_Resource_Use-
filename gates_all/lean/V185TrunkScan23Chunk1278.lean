import V185TrunkScan23Chunk1277

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7571788 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 4, 2, 2]
def baseStart_7571788 : Nat := 118140960795 + 7571788 * 2 ^ 59
def prefixEnd_7571788 : Nat := 4983230072969 + 3 ^ 40 * 7571788 * 2
def baseEnd_7571788 : Nat := 3887966657945726578327987

theorem tailTrace_7571788 : CollatzResearch.WordTrace tailWord_7571788 prefixEnd_7571788 3887966657945726578327987 := by
  unfold tailWord_7571788
  simp only [CollatzResearch.WordTrace]
  refine ⟨138082898146356354640954009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184110530861808472854605345 138082898146356354640954009)
  ·
    refine ⟨103562173609767265980715507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138082898146356354640954009 103562173609767265980715507)
    ·
      refine ⟨155343260414650898971073261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103562173609767265980715507 155343260414650898971073261)
      ·
        refine ⟨58253722655494087114152473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155343260414650898971073261 58253722655494087114152473)
        ·
          refine ⟨43690291991620565335614355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58253722655494087114152473 43690291991620565335614355)
          ·
            refine ⟨65535437987430848003421533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43690291991620565335614355 65535437987430848003421533)
            ·
              refine ⟨24575789245286568001283075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65535437987430848003421533 24575789245286568001283075)
              ·
                refine ⟨36863683867929852001924613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24575789245286568001283075 36863683867929852001924613)
                ·
                  refine ⟨6911940725236847250360865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36863683867929852001924613 6911940725236847250360865)
                  ·
                    refine ⟨5183955543927635437770649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6911940725236847250360865 5183955543927635437770649)
                    ·
                      refine ⟨3887966657945726578327987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5183955543927635437770649 3887966657945726578327987)
                      ·
                        rfl

theorem cell23_7571788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_7571788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571788 prefixEnd_7571788 := by exact prefixLift 7571788
  have htrace : WordTrace (prefixWord ++ tailWord_7571788) baseStart_7571788 baseEnd_7571788 := by
    simpa [prefixWord, tailWord_7571788, baseEnd_7571788] using wordTrace_append hprefix tailTrace_7571788
  have hstable : (prefixWord ++ tailWord_7571788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571788).length < 2 ^ (prefixWord ++ tailWord_7571788).sum := by decide
  have hdescent : baseEnd_7571788 < baseStart_7571788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571794 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 7]
def baseStart_7571794 : Nat := 118140960795 + 7571794 * 2 ^ 59
def prefixEnd_7571794 : Nat := 4983230072969 + 3 ^ 40 * 7571794 * 2
def baseEnd_7571794 : Nat := 431996637647739283872551

theorem tailTrace_7571794 : CollatzResearch.WordTrace tailWord_7571794 prefixEnd_7571794 431996637647739283872551 := by
  unfold tailWord_7571794
  simp only [CollatzResearch.WordTrace]
  refine ⟨69041503782672743076656609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184110676753793981537750957 69041503782672743076656609)
  ·
    refine ⟨51781127837004557307492457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69041503782672743076656609 51781127837004557307492457)
    ·
      refine ⟨38835845877753417980619343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51781127837004557307492457 38835845877753417980619343)
      ·
        refine ⟨58253768816630126970929015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38835845877753417980619343 58253768816630126970929015)
        ·
          refine ⟨87380653224945190456393523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58253768816630126970929015 87380653224945190456393523)
          ·
            refine ⟨131070979837417785684590285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87380653224945190456393523 131070979837417785684590285)
            ·
              refine ⟨49151617439031669631721357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131070979837417785684590285 49151617439031669631721357)
              ·
                refine ⟨18431856539636876111895509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49151617439031669631721357 18431856539636876111895509)
                ·
                  refine ⟨431996637647739283872551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18431856539636876111895509 431996637647739283872551)
                  ·
                    rfl

theorem cell23_7571794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_7571794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571794 prefixEnd_7571794 := by exact prefixLift 7571794
  have htrace : WordTrace (prefixWord ++ tailWord_7571794) baseStart_7571794 baseEnd_7571794 := by
    simpa [prefixWord, tailWord_7571794, baseEnd_7571794] using wordTrace_append hprefix tailTrace_7571794
  have hstable : (prefixWord ++ tailWord_7571794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571794).length < 2 ^ (prefixWord ++ tailWord_7571794).sum := by decide
  have hdescent : baseEnd_7571794 < baseStart_7571794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571824 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 1, 7]
def baseStart_7571824 : Nat := 118140960795 + 7571824 * 2 ^ 59
def prefixEnd_7571824 : Nat := 4983230072969 + 3 ^ 40 * 7571824 * 2
def baseEnd_7571824 : Nat := 1295995047749762812492607

theorem tailTrace_7571824 : CollatzResearch.WordTrace tailWord_7571824 prefixEnd_7571824 1295995047749762812492607 := by
  unfold tailWord_7571824
  simp only [CollatzResearch.WordTrace]
  refine ⟨138083554660291143715109263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184111406213721524953479017 138083554660291143715109263)
  ·
    refine ⟨207125331990436715572663895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138083554660291143715109263 207125331990436715572663895)
    ·
      refine ⟨310687997985655073358995843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207125331990436715572663895 310687997985655073358995843)
      ·
        refine ⟨466031996978482610038493765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310687997985655073358995843 466031996978482610038493765)
        ·
          refine ⟨87380999433465489382217581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466031996978482610038493765 87380999433465489382217581)
          ·
            refine ⟨32767874787549558518331593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87380999433465489382217581 32767874787549558518331593)
            ·
              refine ⟨24575906090662168888748695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32767874787549558518331593 24575906090662168888748695)
              ·
                refine ⟨36863859135993253333123043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24575906090662168888748695 36863859135993253333123043)
                ·
                  refine ⟨55295788703989879999684565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36863859135993253333123043 55295788703989879999684565)
                  ·
                    refine ⟨1295995047749762812492607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55295788703989879999684565 1295995047749762812492607)
                    ·
                      rfl

theorem cell23_7571824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_7571824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571824 prefixEnd_7571824 := by exact prefixLift 7571824
  have htrace : WordTrace (prefixWord ++ tailWord_7571824) baseStart_7571824 baseEnd_7571824 := by
    simpa [prefixWord, tailWord_7571824, baseEnd_7571824] using wordTrace_append hprefix tailTrace_7571824
  have hstable : (prefixWord ++ tailWord_7571824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571824).length < 2 ^ (prefixWord ++ tailWord_7571824).sum := by decide
  have hdescent : baseEnd_7571824 < baseStart_7571824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571841 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 4, 5]
def baseStart_7571841 : Nat := 118140960795 + 7571841 * 2 ^ 59
def prefixEnd_7571841 : Nat := 4983230072969 + 3 ^ 40 * 7571841 * 2
def baseEnd_7571841 : Nat := 1295997957473471623655081

theorem tailTrace_7571841 : CollatzResearch.WordTrace tailWord_7571841 prefixEnd_7571841 1295997957473471623655081 := by
  unfold tailWord_7571841
  simp only [CollatzResearch.WordTrace]
  refine ⟨276167729361520699333587377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184111819574347132889058251 276167729361520699333587377)
  ·
    refine ⟨207125797021140524500190533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276167729361520699333587377 207125797021140524500190533)
    ·
      refine ⟨38836086941463848343785725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207125797021140524500190533 38836086941463848343785725)
      ·
        refine ⟨14563532603048943128919647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38836086941463848343785725 14563532603048943128919647)
        ·
          refine ⟨21845298904573414693379471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14563532603048943128919647 21845298904573414693379471)
          ·
            refine ⟨32767948356860122040069207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21845298904573414693379471 32767948356860122040069207)
            ·
              refine ⟨49151922535290183060103811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32767948356860122040069207 49151922535290183060103811)
              ·
                refine ⟨73727883802935274590155717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49151922535290183060103811 73727883802935274590155717)
                ·
                  refine ⟨13823978213050363985654197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73727883802935274590155717 13823978213050363985654197)
                  ·
                    refine ⟨1295997957473471623655081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13823978213050363985654197 1295997957473471623655081)
                    ·
                      rfl

theorem cell23_7571841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_7571841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571841 prefixEnd_7571841 := by exact prefixLift 7571841
  have htrace : WordTrace (prefixWord ++ tailWord_7571841) baseStart_7571841 baseEnd_7571841 := by
    simpa [prefixWord, tailWord_7571841, baseEnd_7571841] using wordTrace_append hprefix tailTrace_7571841
  have hstable : (prefixWord ++ tailWord_7571841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571841).length < 2 ^ (prefixWord ++ tailWord_7571841).sum := by decide
  have hdescent : baseEnd_7571841 < baseStart_7571841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571861 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_7571861 : Nat := 118140960795 + 7571861 * 2 ^ 59
def prefixEnd_7571861 : Nat := 4983230072969 + 3 ^ 40 * 7571861 * 2
def baseEnd_7571861 : Nat := 3888004142033504792715151

theorem tailTrace_7571861 : CollatzResearch.WordTrace tailWord_7571861 prefixEnd_7571861 3888004142033504792715151 := by
  unfold tailWord_7571861
  simp only [CollatzResearch.WordTrace]
  refine ⟨276168458821448242749315437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184112305880965495166210291 276168458821448242749315437)
  ·
    refine ⟨103563172058043091030993289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276168458821448242749315437 103563172058043091030993289)
    ·
      refine ⟨77672379043532318273244967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103563172058043091030993289 77672379043532318273244967)
      ·
        refine ⟨116508568565298477409867451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77672379043532318273244967 116508568565298477409867451)
        ·
          refine ⟨174762852847947716114801177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116508568565298477409867451 174762852847947716114801177)
          ·
            refine ⟨131072139635960787086100883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174762852847947716114801177 131072139635960787086100883)
            ·
              refine ⟨196608209453941180629151325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131072139635960787086100883 196608209453941180629151325)
              ·
                refine ⟨73728078545227942735931747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196608209453941180629151325 73728078545227942735931747)
                ·
                  refine ⟨110592117817841914103897621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73728078545227942735931747 110592117817841914103897621)
                  ·
                    refine ⟨5184005522711339723620201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110592117817841914103897621 5184005522711339723620201)
                    ·
                      refine ⟨3888004142033504792715151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184005522711339723620201 3888004142033504792715151)
                      ·
                        rfl

theorem cell23_7571861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_7571861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571861 prefixEnd_7571861 := by exact prefixLift 7571861
  have htrace : WordTrace (prefixWord ++ tailWord_7571861) baseStart_7571861 baseEnd_7571861 := by
    simpa [prefixWord, tailWord_7571861, baseEnd_7571861] using wordTrace_append hprefix tailTrace_7571861
  have hstable : (prefixWord ++ tailWord_7571861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571861).length < 2 ^ (prefixWord ++ tailWord_7571861).sum := by decide
  have hdescent : baseEnd_7571861 < baseStart_7571861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571871 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 5, 4]
def baseStart_7571871 : Nat := 118140960795 + 7571871 * 2 ^ 59
def prefixEnd_7571871 : Nat := 4983230072969 + 3 ^ 40 * 7571871 * 2
def baseEnd_7571871 : Nat := 1296003092280016584530035

theorem tailTrace_7571871 : CollatzResearch.WordTrace tailWord_7571871 prefixEnd_7571871 1296003092280016584530035 := by
  unfold tailWord_7571871
  simp only [CollatzResearch.WordTrace]
  refine ⟨276168823551412014457179467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184112549034274676304786311 276168823551412014457179467)
  ·
    refine ⟨414253235327118021685769201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276168823551412014457179467 414253235327118021685769201)
    ·
      refine ⟨310689926495338516264326901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414253235327118021685769201 310689926495338516264326901)
      ·
        refine ⟨29127180608937985899780647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310689926495338516264326901 29127180608937985899780647)
        ·
          refine ⟨43690770913406978849670971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29127180608937985899780647 43690770913406978849670971)
          ·
            refine ⟨65536156370110468274506457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43690770913406978849670971 65536156370110468274506457)
            ·
              refine ⟨49152117277582851205879843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65536156370110468274506457 49152117277582851205879843)
              ·
                refine ⟨73728175916374276808819765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49152117277582851205879843 73728175916374276808819765)
                ·
                  refine ⟨6912016492160088450826853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73728175916374276808819765 6912016492160088450826853)
                  ·
                    refine ⟨1296003092280016584530035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6912016492160088450826853 1296003092280016584530035)
                    ·
                      rfl

theorem cell23_7571871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 4].length) (baseStart_7571871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571871 prefixEnd_7571871 := by exact prefixLift 7571871
  have htrace : WordTrace (prefixWord ++ tailWord_7571871) baseStart_7571871 baseEnd_7571871 := by
    simpa [prefixWord, tailWord_7571871, baseEnd_7571871] using wordTrace_append hprefix tailTrace_7571871
  have hstable : (prefixWord ++ tailWord_7571871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571871).length < 2 ^ (prefixWord ++ tailWord_7571871).sum := by decide
  have hdescent : baseEnd_7571871 < baseStart_7571871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571901 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 6]
def baseStart_7571901 : Nat := 118140960795 + 7571901 * 2 ^ 59
def prefixEnd_7571901 : Nat := 4983230072969 + 3 ^ 40 * 7571901 * 2
def baseEnd_7571901 : Nat := 432002742362187181801663

theorem tailTrace_7571901 : CollatzResearch.WordTrace tailWord_7571901 prefixEnd_7571901 432002742362187181801663 := by
  unfold tailWord_7571901
  simp only [CollatzResearch.WordTrace]
  refine ⟨276169917741303329580771557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184113278494202219720514371 276169917741303329580771557)
  ·
    refine ⟨51781859576494374296394667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276169917741303329580771557 51781859576494374296394667)
    ·
      refine ⟨77672789364741561444592001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51781859576494374296394667 77672789364741561444592001)
      ·
        refine ⟨58254592023556171083444001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77672789364741561444592001 58254592023556171083444001)
        ·
          refine ⟨43690944017667128312583001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58254592023556171083444001 43690944017667128312583001)
          ·
            refine ⟨32768208013250346234437251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43690944017667128312583001 32768208013250346234437251)
            ·
              refine ⟨49152312019875519351655877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32768208013250346234437251 49152312019875519351655877)
              ·
                refine ⟨9216058503726659878435477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49152312019875519351655877 9216058503726659878435477)
                ·
                  refine ⟨432002742362187181801663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9216058503726659878435477 432002742362187181801663)
                  ·
                    rfl

theorem cell23_7571901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_7571901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571901 prefixEnd_7571901 := by exact prefixLift 7571901
  have htrace : WordTrace (prefixWord ++ tailWord_7571901) baseStart_7571901 baseEnd_7571901 := by
    simpa [prefixWord, tailWord_7571901, baseEnd_7571901] using wordTrace_append hprefix tailTrace_7571901
  have hstable : (prefixWord ++ tailWord_7571901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571901).length < 2 ^ (prefixWord ++ tailWord_7571901).sum := by decide
  have hdescent : baseEnd_7571901 < baseStart_7571901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571904 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_7571904 : Nat := 118140960795 + 7571904 * 2 ^ 59
def prefixEnd_7571904 : Nat := 4983230072969 + 3 ^ 40 * 7571904 * 2
def baseEnd_7571904 : Nat := 3888026221701648124477453

theorem tailTrace_7571904 : CollatzResearch.WordTrace tailWord_7571904 prefixEnd_7571904 3888026221701648124477453 := by
  unfold tailWord_7571904
  simp only [CollatzResearch.WordTrace]
  refine ⟨138085013580146230546565383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184113351440194974062087177 138085013580146230546565383)
  ·
    refine ⟨207127520370219345819848075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138085013580146230546565383 207127520370219345819848075)
    ·
      refine ⟨310691280555329018729772113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207127520370219345819848075 310691280555329018729772113)
      ·
        refine ⟨233018460416496764047329085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310691280555329018729772113 233018460416496764047329085)
        ·
          refine ⟨87381922656186286517748407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233018460416496764047329085 87381922656186286517748407)
          ·
            refine ⟨131072883984279429776622611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87381922656186286517748407 131072883984279429776622611)
            ·
              refine ⟨196609325976419144664933917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131072883984279429776622611 196609325976419144664933917)
              ·
                refine ⟨73728497241157179249350219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196609325976419144664933917 73728497241157179249350219)
                ·
                  refine ⟨110592745861735768874025329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73728497241157179249350219 110592745861735768874025329)
                  ·
                    refine ⟨82944559396301826655518997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110592745861735768874025329 82944559396301826655518997)
                    ·
                      refine ⟨3888026221701648124477453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82944559396301826655518997 3888026221701648124477453)
                      ·
                        rfl

theorem cell23_7571904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_7571904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571904 prefixEnd_7571904 := by exact prefixLift 7571904
  have htrace : WordTrace (prefixWord ++ tailWord_7571904) baseStart_7571904 baseEnd_7571904 := by
    simpa [prefixWord, tailWord_7571904, baseEnd_7571904] using wordTrace_append hprefix tailTrace_7571904
  have hstable : (prefixWord ++ tailWord_7571904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571904).length < 2 ^ (prefixWord ++ tailWord_7571904).sum := by decide
  have hdescent : baseEnd_7571904 < baseStart_7571904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7571971 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 5]
def baseStart_7571971 : Nat := 118140960795 + 7571971 * 2 ^ 59
def prefixEnd_7571971 : Nat := 4983230072969 + 3 ^ 40 * 7571971 * 2
def baseEnd_7571971 : Nat := 3888060624905499362339645

theorem tailTrace_7571971 : CollatzResearch.WordTrace tailWord_7571971 prefixEnd_7571971 3888060624905499362339645 := by
  unfold tailWord_7571971
  simp only [CollatzResearch.WordTrace]
  refine ⟨276172470851049731535819767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184114980567366487690546511 276172470851049731535819767)
  ·
    refine ⟨414258706276574597303729651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276172470851049731535819767 414258706276574597303729651)
    ·
      refine ⟨621388059414861895955594477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414258706276574597303729651 621388059414861895955594477)
      ·
        refine ⟨233020522280573210983347929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 621388059414861895955594477 233020522280573210983347929)
        ·
          refine ⟨174765391710429908237510947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233020522280573210983347929 174765391710429908237510947)
          ·
            refine ⟨262148087565644862356266421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174765391710429908237510947 262148087565644862356266421)
            ·
              refine ⟨24576383209279205845899977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262148087565644862356266421 24576383209279205845899977)
              ·
                refine ⟨18432287406959404384424983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24576383209279205845899977 18432287406959404384424983)
                ·
                  refine ⟨27648431110439106576637475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18432287406959404384424983 27648431110439106576637475)
                  ·
                    refine ⟨41472646665658659864956213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27648431110439106576637475 41472646665658659864956213)
                    ·
                      refine ⟨3888060624905499362339645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41472646665658659864956213 3888060624905499362339645)
                      ·
                        rfl

theorem cell23_7571971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_7571971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7571971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7571971 prefixEnd_7571971 := by exact prefixLift 7571971
  have htrace : WordTrace (prefixWord ++ tailWord_7571971) baseStart_7571971 baseEnd_7571971 := by
    simpa [prefixWord, tailWord_7571971, baseEnd_7571971] using wordTrace_append hprefix tailTrace_7571971
  have hstable : (prefixWord ++ tailWord_7571971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7571971).length < 2 ^ (prefixWord ++ tailWord_7571971).sum := by decide
  have hdescent : baseEnd_7571971 < baseStart_7571971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7571971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572008 : List Nat := [2, 1, 5, 2, 1, 3, 9]
def baseStart_7572008 : Nat := 118140960795 + 7572008 * 2 ^ 59
def prefixEnd_7572008 : Nat := 4983230072969 + 3 ^ 40 * 7572008 * 2
def baseEnd_7572008 : Nat := 48000983008515008858975

theorem tailTrace_7572008 : CollatzResearch.WordTrace tailWord_7572008 prefixEnd_7572008 48000983008515008858975 := by
  unfold tailWord_7572008
  simp only [CollatzResearch.WordTrace]
  refine ⟨138086910175957843427458339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184115880234610457903277785 138086910175957843427458339)
  ·
    refine ⟨207130365263936765141187509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138086910175957843427458339 207130365263936765141187509)
    ·
      refine ⟨19418471743494071731986329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207130365263936765141187509 19418471743494071731986329)
      ·
        refine ⟨14563853807620553798989747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19418471743494071731986329 14563853807620553798989747)
        ·
          refine ⟨21845780711430830698484621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14563853807620553798989747 21845780711430830698484621)
          ·
            refine ⟨8192167766786561511931733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21845780711430830698484621 8192167766786561511931733)
            ·
              refine ⟨48000983008515008858975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8192167766786561511931733 48000983008515008858975)
              ·
                rfl

theorem cell23_7572008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 9].length) (baseStart_7572008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572008 prefixEnd_7572008 := by exact prefixLift 7572008
  have htrace : WordTrace (prefixWord ++ tailWord_7572008) baseStart_7572008 baseEnd_7572008 := by
    simpa [prefixWord, tailWord_7572008, baseEnd_7572008] using wordTrace_append hprefix tailTrace_7572008
  have hstable : (prefixWord ++ tailWord_7572008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572008).length < 2 ^ (prefixWord ++ tailWord_7572008).sum := by decide
  have hdescent : baseEnd_7572008 < baseStart_7572008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572013 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7572013 : Nat := 118140960795 + 7572013 * 2 ^ 59
def prefixEnd_7572013 : Nat := 4983230072969 + 3 ^ 40 * 7572013 * 2
def baseEnd_7572013 : Nat := 3888082191092988198014453

theorem tailTrace_7572013 : CollatzResearch.WordTrace tailWord_7572013 prefixEnd_7572013 3888082191092988198014453 := by
  unfold tailWord_7572013
  simp only [CollatzResearch.WordTrace]
  refine ⟨276174002716897572708848693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184116001811265048472565795 276174002716897572708848693)
  ·
    refine ⟨25891312754709147441454565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276174002716897572708848693 25891312754709147441454565)
    ·
      refine ⟨4854621141507965145272731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25891312754709147441454565 4854621141507965145272731)
      ·
        refine ⟨7281931712261947717909097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854621141507965145272731 7281931712261947717909097)
        ·
          refine ⟨5461448784196460788431823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7281931712261947717909097 5461448784196460788431823)
          ·
            refine ⟨8192173176294691182647735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461448784196460788431823 8192173176294691182647735)
            ·
              refine ⟨12288259764442036773971603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8192173176294691182647735 12288259764442036773971603)
              ·
                refine ⟨18432389646663055160957405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12288259764442036773971603 18432389646663055160957405)
                ·
                  refine ⟨6912146117498645685359027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18432389646663055160957405 6912146117498645685359027)
                  ·
                    refine ⟨10368219176247968528038541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6912146117498645685359027 10368219176247968528038541)
                    ·
                      refine ⟨3888082191092988198014453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10368219176247968528038541 3888082191092988198014453)
                      ·
                        rfl

theorem cell23_7572013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7572013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572013 prefixEnd_7572013 := by exact prefixLift 7572013
  have htrace : WordTrace (prefixWord ++ tailWord_7572013) baseStart_7572013 baseEnd_7572013 := by
    simpa [prefixWord, tailWord_7572013, baseEnd_7572013] using wordTrace_append hprefix tailTrace_7572013
  have hstable : (prefixWord ++ tailWord_7572013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572013).length < 2 ^ (prefixWord ++ tailWord_7572013).sum := by decide
  have hdescent : baseEnd_7572013 < baseStart_7572013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572019 : List Nat := [1, 1, 1, 2, 4, 2, 5, 2, 1, 2, 2]
def baseStart_7572019 : Nat := 118140960795 + 7572019 * 2 ^ 59
def prefixEnd_7572019 : Nat := 4983230072969 + 3 ^ 40 * 7572019 * 2
def baseEnd_7572019 : Nat := 3888085271976915174539425

theorem tailTrace_7572019 : CollatzResearch.WordTrace tailWord_7572019 prefixEnd_7572019 3888085271976915174539425 := by
  unfold tailWord_7572019
  simp only [CollatzResearch.WordTrace]
  refine ⟨276174221554875835733567111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184116147703250557155711407 276174221554875835733567111)
  ·
    refine ⟨414261332332313753600350667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276174221554875835733567111 414261332332313753600350667)
    ·
      refine ⟨621391998498470630400526001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414261332332313753600350667 621391998498470630400526001)
      ·
        refine ⟨466043998873852972800394501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621391998498470630400526001 466043998873852972800394501)
        ·
          refine ⟨87383249788847432400073969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466043998873852972800394501 87383249788847432400073969)
          ·
            refine ⟨65537437341635574300055477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87383249788847432400073969 65537437341635574300055477)
            ·
              refine ⟨6144134750778335090630201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65537437341635574300055477 6144134750778335090630201)
              ·
                refine ⟨4608101063083751317972651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6144134750778335090630201 4608101063083751317972651)
                ·
                  refine ⟨6912151594625626976958977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608101063083751317972651 6912151594625626976958977)
                  ·
                    refine ⟨5184113695969220232719233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6912151594625626976958977 5184113695969220232719233)
                    ·
                      refine ⟨3888085271976915174539425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184113695969220232719233 3888085271976915174539425)
                      ·
                        rfl

theorem cell23_7572019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 2, 2].length) (baseStart_7572019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572019 prefixEnd_7572019 := by exact prefixLift 7572019
  have htrace : WordTrace (prefixWord ++ tailWord_7572019) baseStart_7572019 baseEnd_7572019 := by
    simpa [prefixWord, tailWord_7572019, baseEnd_7572019] using wordTrace_append hprefix tailTrace_7572019
  have hstable : (prefixWord ++ tailWord_7572019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572019).length < 2 ^ (prefixWord ++ tailWord_7572019).sum := by decide
  have hdescent : baseEnd_7572019 < baseStart_7572019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572021 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_7572021 : Nat := 118140960795 + 7572021 * 2 ^ 59
def prefixEnd_7572021 : Nat := 4983230072969 + 3 ^ 40 * 7572021 * 2
def baseEnd_7572021 : Nat := 1296028766312741388904805

theorem tailTrace_7572021 : CollatzResearch.WordTrace tailWord_7572021 prefixEnd_7572021 1296028766312741388904805 := by
  unfold tailWord_7572021
  simp only [CollatzResearch.WordTrace]
  refine ⟨276174294500868590075139917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184116196333912393383426611 276174294500868590075139917)
  ·
    refine ⟨103565360437825721278177469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276174294500868590075139917 103565360437825721278177469)
    ·
      refine ⟨38837010164184645479316551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103565360437825721278177469 38837010164184645479316551)
      ·
        refine ⟨58255515246276968218974827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38837010164184645479316551 58255515246276968218974827)
        ·
          refine ⟨87383272869415452328462241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58255515246276968218974827 87383272869415452328462241)
          ·
            refine ⟨65537454652061589246346681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87383272869415452328462241 65537454652061589246346681)
            ·
              refine ⟨49153090989046191934760011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65537454652061589246346681 49153090989046191934760011)
              ·
                refine ⟨73729636483569287902140017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49153090989046191934760011 73729636483569287902140017)
                ·
                  refine ⟨55297227362676965926605013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73729636483569287902140017 55297227362676965926605013)
                  ·
                    refine ⟨1296028766312741388904805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55297227362676965926605013 1296028766312741388904805)
                    ·
                      rfl

theorem cell23_7572021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_7572021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572021 prefixEnd_7572021 := by exact prefixLift 7572021
  have htrace : WordTrace (prefixWord ++ tailWord_7572021) baseStart_7572021 baseEnd_7572021 := by
    simpa [prefixWord, tailWord_7572021, baseEnd_7572021] using wordTrace_append hprefix tailTrace_7572021
  have hstable : (prefixWord ++ tailWord_7572021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572021).length < 2 ^ (prefixWord ++ tailWord_7572021).sum := by decide
  have hdescent : baseEnd_7572021 < baseStart_7572021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572036 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7572036 : Nat := 118140960795 + 7572036 * 2 ^ 59
def prefixEnd_7572036 : Nat := 4983230072969 + 3 ^ 40 * 7572036 * 2
def baseEnd_7572036 : Nat := 3888094001148041608026847

theorem tailTrace_7572036 : CollatzResearch.WordTrace tailWord_7572036 prefixEnd_7572036 3888094001148041608026847 := by
  unfold tailWord_7572036
  simp only [CollatzResearch.WordTrace]
  refine ⟨138087420797907123818467981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184116561063876165091290641 138087420797907123818467981)
  ·
    refine ⟨51782782799215171431925493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138087420797907123818467981 51782782799215171431925493)
    ·
      refine ⟨4854635887426422321743015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51782782799215171431925493 4854635887426422321743015)
      ·
        refine ⟨7281953831139633482614523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854635887426422321743015 7281953831139633482614523)
        ·
          refine ⟨10922930746709450223921785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281953831139633482614523 10922930746709450223921785)
          ·
            refine ⟨8192198060032087667941339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10922930746709450223921785 8192198060032087667941339)
            ·
              refine ⟨12288297090048131501912009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8192198060032087667941339 12288297090048131501912009)
              ·
                refine ⟨9216222817536098626434007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12288297090048131501912009 9216222817536098626434007)
                ·
                  refine ⟨13824334226304147939651011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9216222817536098626434007 13824334226304147939651011)
                  ·
                    refine ⟨20736501339456221909476517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13824334226304147939651011 20736501339456221909476517)
                    ·
                      refine ⟨3888094001148041608026847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20736501339456221909476517 3888094001148041608026847)
                      ·
                        rfl

theorem cell23_7572036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7572036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572036 prefixEnd_7572036 := by exact prefixLift 7572036
  have htrace : WordTrace (prefixWord ++ tailWord_7572036) baseStart_7572036 baseEnd_7572036 := by
    simpa [prefixWord, tailWord_7572036, baseEnd_7572036] using wordTrace_append hprefix tailTrace_7572036
  have hstable : (prefixWord ++ tailWord_7572036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572036).length < 2 ^ (prefixWord ++ tailWord_7572036).sum := by decide
  have hdescent : baseEnd_7572036 < baseStart_7572036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572071 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_7572071 : Nat := 118140960795 + 7572071 * 2 ^ 59
def prefixEnd_7572071 : Nat := 4983230072969 + 3 ^ 40 * 7572071 * 2
def baseEnd_7572071 : Nat := 3888111972970948971089185

theorem tailTrace_7572071 : CollatzResearch.WordTrace tailWord_7572071 prefixEnd_7572071 3888111972970948971089185 := by
  unfold tailWord_7572071
  simp only [CollatzResearch.WordTrace]
  refine ⟨276176118150687448614460067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184117412100458299076306711 276176118150687448614460067)
  ·
    refine ⟨414264177226031172921690101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276176118150687448614460067 414264177226031172921690101)
    ·
      refine ⟨38837266614940422461408447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 414264177226031172921690101 38837266614940422461408447)
      ·
        refine ⟨58255899922410633692112671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38837266614940422461408447 58255899922410633692112671)
        ·
          refine ⟨87383849883615950538169007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58255899922410633692112671 87383849883615950538169007)
          ·
            refine ⟨131075774825423925807253511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87383849883615950538169007 131075774825423925807253511)
            ·
              refine ⟨196613662238135888710880267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131075774825423925807253511 196613662238135888710880267)
              ·
                refine ⟨294920493357203833066320401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196613662238135888710880267 294920493357203833066320401)
                ·
                  refine ⟨221190370017902874799740301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294920493357203833066320401 221190370017902874799740301)
                  ·
                    refine ⟨82946388756713578049902613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221190370017902874799740301 82946388756713578049902613)
                    ·
                      refine ⟨3888111972970948971089185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82946388756713578049902613 3888111972970948971089185)
                      ·
                        rfl

theorem cell23_7572071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_7572071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572071 prefixEnd_7572071 := by exact prefixLift 7572071
  have htrace : WordTrace (prefixWord ++ tailWord_7572071) baseStart_7572071 baseEnd_7572071 := by
    simpa [prefixWord, tailWord_7572071, baseEnd_7572071] using wordTrace_append hprefix tailTrace_7572071
  have hstable : (prefixWord ++ tailWord_7572071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572071).length < 2 ^ (prefixWord ++ tailWord_7572071).sum := by decide
  have hdescent : baseEnd_7572071 < baseStart_7572071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572085 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7572085 : Nat := 118140960795 + 7572085 * 2 ^ 59
def prefixEnd_7572085 : Nat := 4983230072969 + 3 ^ 40 * 7572085 * 2
def baseEnd_7572085 : Nat := 1296039720566703972104707

theorem tailTrace_7572085 : CollatzResearch.WordTrace tailWord_7572085 prefixEnd_7572085 1296039720566703972104707 := by
  unfold tailWord_7572085
  simp only [CollatzResearch.WordTrace]
  refine ⟨276176628772636729005469709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184117752515091152670313139 276176628772636729005469709)
  ·
    refine ⟨103566235789738773377051141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276176628772636729005469709 103566235789738773377051141)
    ·
      refine ⟨19418669210576020008197089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103566235789738773377051141 19418669210576020008197089)
      ·
        refine ⟨14564001907932015006147817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19418669210576020008197089 14564001907932015006147817)
        ·
          refine ⟨10923001430949011254610863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14564001907932015006147817 10923001430949011254610863)
          ·
            refine ⟨16384502146423516881916295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923001430949011254610863 16384502146423516881916295)
            ·
              refine ⟨24576753219635275322874443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16384502146423516881916295 24576753219635275322874443)
              ·
                refine ⟨36865129829452912984311665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24576753219635275322874443 36865129829452912984311665)
                ·
                  refine ⟨27648847372089684738233749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36865129829452912984311665 27648847372089684738233749)
                  ·
                    refine ⟨1296039720566703972104707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27648847372089684738233749 1296039720566703972104707)
                    ·
                      rfl

theorem cell23_7572085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7572085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572085 prefixEnd_7572085 := by exact prefixLift 7572085
  have htrace : WordTrace (prefixWord ++ tailWord_7572085) baseStart_7572085 baseEnd_7572085 := by
    simpa [prefixWord, tailWord_7572085, baseEnd_7572085] using wordTrace_append hprefix tailTrace_7572085
  have hstable : (prefixWord ++ tailWord_7572085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572085).length < 2 ^ (prefixWord ++ tailWord_7572085).sum := by decide
  have hdescent : baseEnd_7572085 < baseStart_7572085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572092 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_7572092 : Nat := 118140960795 + 7572092 * 2 ^ 59
def prefixEnd_7572092 : Nat := 4983230072969 + 3 ^ 40 * 7572092 * 2
def baseEnd_7572092 : Nat := 3888122756064693388926589

theorem tailTrace_7572092 : CollatzResearch.WordTrace tailWord_7572092 prefixEnd_7572092 3888122756064693388926589 := by
  unfold tailWord_7572092
  simp only [CollatzResearch.WordTrace]
  refine ⟨138088442041805684600487265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184117922722407579467316353 138088442041805684600487265)
  ·
    refine ⟨103566331531354263450365449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138088442041805684600487265 103566331531354263450365449)
    ·
      refine ⟨77674748648515697587774087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103566331531354263450365449 77674748648515697587774087)
      ·
        refine ⟨116512122972773546381661131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77674748648515697587774087 116512122972773546381661131)
        ·
          refine ⟨174768184459160319572491697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116512122972773546381661131 174768184459160319572491697)
          ·
            refine ⟨131076138344370239679368773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174768184459160319572491697 131076138344370239679368773)
            ·
              refine ⟨24576775939569419939881645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131076138344370239679368773 24576775939569419939881645)
              ·
                refine ⟨9216290977338532477455617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24576775939569419939881645 9216290977338532477455617)
                ·
                  refine ⟨6912218233003899358091713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9216290977338532477455617 6912218233003899358091713)
                  ·
                    refine ⟨5184163674752924518568785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6912218233003899358091713 5184163674752924518568785)
                    ·
                      refine ⟨3888122756064693388926589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184163674752924518568785 3888122756064693388926589)
                      ·
                        rfl

theorem cell23_7572092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_7572092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572092 prefixEnd_7572092 := by exact prefixLift 7572092
  have htrace : WordTrace (prefixWord ++ tailWord_7572092) baseStart_7572092 baseEnd_7572092 := by
    simpa [prefixWord, tailWord_7572092, baseEnd_7572092] using wordTrace_append hprefix tailTrace_7572092
  have hstable : (prefixWord ++ tailWord_7572092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572092).length < 2 ^ (prefixWord ++ tailWord_7572092).sum := by decide
  have hdescent : baseEnd_7572092 < baseStart_7572092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572111 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 1, 7]
def baseStart_7572111 : Nat := 118140960795 + 7572111 * 2 ^ 59
def prefixEnd_7572111 : Nat := 4983230072969 + 3 ^ 40 * 7572111 * 2
def baseEnd_7572111 : Nat := 1296044170732376271529667

theorem tailTrace_7572111 : CollatzResearch.WordTrace tailWord_7572111 prefixEnd_7572111 1296044170732376271529667 := by
  unfold tailWord_7572111
  simp only [CollatzResearch.WordTrace]
  refine ⟨276177577070542535445916187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184118384713695023630610791 276177577070542535445916187)
  ·
    refine ⟨414266365605813803168874281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276177577070542535445916187 414266365605813803168874281)
    ·
      refine ⟨310699774204360352376655711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414266365605813803168874281 310699774204360352376655711)
      ·
        refine ⟨466049661306540528564983567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310699774204360352376655711 466049661306540528564983567)
        ·
          refine ⟨699074491959810792847475351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466049661306540528564983567 699074491959810792847475351)
          ·
            refine ⟨1048611737939716189271213027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699074491959810792847475351 1048611737939716189271213027)
            ·
              refine ⟨1572917606909574283906819541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048611737939716189271213027 1572917606909574283906819541)
              ·
                refine ⟨36865256411943147279066083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1572917606909574283906819541 36865256411943147279066083)
                ·
                  refine ⟨55297884617914720918599125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36865256411943147279066083 55297884617914720918599125)
                  ·
                    refine ⟨1296044170732376271529667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55297884617914720918599125 1296044170732376271529667)
                    ·
                      rfl

theorem cell23_7572111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_7572111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572111 prefixEnd_7572111 := by exact prefixLift 7572111
  have htrace : WordTrace (prefixWord ++ tailWord_7572111) baseStart_7572111 baseEnd_7572111 := by
    simpa [prefixWord, tailWord_7572111, baseEnd_7572111] using wordTrace_append hprefix tailTrace_7572111
  have hstable : (prefixWord ++ tailWord_7572111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572111).length < 2 ^ (prefixWord ++ tailWord_7572111).sum := by decide
  have hdescent : baseEnd_7572111 < baseStart_7572111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572142 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_7572142 : Nat := 118140960795 + 7572142 * 2 ^ 59
def prefixEnd_7572142 : Nat := 4983230072969 + 3 ^ 40 * 7572142 * 2
def baseEnd_7572142 : Nat := 3888148430097418193301359

theorem tailTrace_7572142 : CollatzResearch.WordTrace tailWord_7572142 prefixEnd_7572142 3888148430097418193301359 := by
  unfold tailWord_7572142
  simp only [CollatzResearch.WordTrace]
  refine ⟨34522338466678778467536835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184119138488953485160196453 34522338466678778467536835)
  ·
    refine ⟨51783507700018167701305253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34522338466678778467536835 51783507700018167701305253)
    ·
      refine ⟨9709407693753406443994735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51783507700018167701305253 9709407693753406443994735)
      ·
        refine ⟨14564111540630109665992103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9709407693753406443994735 14564111540630109665992103)
        ·
          refine ⟨21846167310945164498988155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14564111540630109665992103 21846167310945164498988155)
          ·
            refine ⟨32769250966417746748482233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21846167310945164498988155 32769250966417746748482233)
            ·
              refine ⟨24576938224813310061361675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32769250966417746748482233 24576938224813310061361675)
              ·
                refine ⟨36865407337219965092042513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24576938224813310061361675 36865407337219965092042513)
                ·
                  refine ⟨27649055502914973819031885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36865407337219965092042513 27649055502914973819031885)
                  ·
                    refine ⟨10368395813593115182136957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27649055502914973819031885 10368395813593115182136957)
                    ·
                      refine ⟨3888148430097418193301359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10368395813593115182136957 3888148430097418193301359)
                      ·
                        rfl

theorem cell23_7572142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_7572142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572142 prefixEnd_7572142 := by exact prefixLift 7572142
  have htrace : WordTrace (prefixWord ++ tailWord_7572142) baseStart_7572142 baseEnd_7572142 := by
    simpa [prefixWord, tailWord_7572142, baseEnd_7572142] using wordTrace_append hprefix tailTrace_7572142
  have hstable : (prefixWord ++ tailWord_7572142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572142).length < 2 ^ (prefixWord ++ tailWord_7572142).sum := by decide
  have hdescent : baseEnd_7572142 < baseStart_7572142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572158 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7572158 : Nat := 118140960795 + 7572158 * 2 ^ 59
def prefixEnd_7572158 : Nat := 4983230072969 + 3 ^ 40 * 7572158 * 2
def baseEnd_7572158 : Nat := 1296052215262630043567095

theorem tailTrace_7572158 : CollatzResearch.WordTrace tailWord_7572158 prefixEnd_7572158 1296052215262630043567095 := by
  unfold tailWord_7572158
  simp only [CollatzResearch.WordTrace]
  refine ⟨34522411412671532809109641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184119527534248174981918085 34522411412671532809109641)
  ·
    refine ⟨25891808559503649606832231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34522411412671532809109641 25891808559503649606832231)
    ·
      refine ⟨38837712839255474410248347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25891808559503649606832231 38837712839255474410248347)
      ·
        refine ⟨58256569258883211615372521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38837712839255474410248347 58256569258883211615372521)
        ·
          refine ⟨43692426944162408711529391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58256569258883211615372521 43692426944162408711529391)
          ·
            refine ⟨65538640416243613067294087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43692426944162408711529391 65538640416243613067294087)
            ·
              refine ⟨98307960624365419600941131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65538640416243613067294087 98307960624365419600941131)
              ·
                refine ⟨147461940936548129401411697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98307960624365419600941131 147461940936548129401411697)
                ·
                  refine ⟨110596455702411097051058773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147461940936548129401411697 110596455702411097051058773)
                  ·
                    refine ⟨1296052215262630043567095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110596455702411097051058773 1296052215262630043567095)
                    ·
                      rfl

theorem cell23_7572158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7572158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572158 prefixEnd_7572158 := by exact prefixLift 7572158
  have htrace : WordTrace (prefixWord ++ tailWord_7572158) baseStart_7572158 baseEnd_7572158 := by
    simpa [prefixWord, tailWord_7572158, baseEnd_7572158] using wordTrace_append hprefix tailTrace_7572158
  have hstable : (prefixWord ++ tailWord_7572158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572158).length < 2 ^ (prefixWord ++ tailWord_7572158).sum := by decide
  have hdescent : baseEnd_7572158 < baseStart_7572158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572185 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 3]
def baseStart_7572185 : Nat := 118140960795 + 7572185 * 2 ^ 59
def prefixEnd_7572185 : Nat := 4983230072969 + 3 ^ 40 * 7572185 * 2
def baseEnd_7572185 : Nat := 3888170509765561525063661

theorem tailTrace_7572185 : CollatzResearch.WordTrace tailWord_7572185 prefixEnd_7572185 3888170509765561525063661 := by
  unfold tailWord_7572185
  simp only [CollatzResearch.WordTrace]
  refine ⟨276180276072274446084110009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184120184048182964056073339 276180276072274446084110009)
  ·
    refine ⟨207135207054205834563082507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276180276072274446084110009 207135207054205834563082507)
    ·
      refine ⟨310702810581308751844623761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207135207054205834563082507 310702810581308751844623761)
      ·
        refine ⟨233027107935981563883467821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310702810581308751844623761 233027107935981563883467821)
        ·
          refine ⟨87385165475993086456300433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233027107935981563883467821 87385165475993086456300433)
          ·
            refine ⟨65538874106994814842225325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87385165475993086456300433 65538874106994814842225325)
            ·
              refine ⟨24577077790123055565834497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65538874106994814842225325 24577077790123055565834497)
              ·
                refine ⟨18432808342592291674375873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24577077790123055565834497 18432808342592291674375873)
                ·
                  refine ⟨13824606256944218755781905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18432808342592291674375873 13824606256944218755781905)
                  ·
                    refine ⟨10368454692708164066836429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13824606256944218755781905 10368454692708164066836429)
                    ·
                      refine ⟨3888170509765561525063661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10368454692708164066836429 3888170509765561525063661)
                      ·
                        rfl

theorem cell23_7572185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_7572185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572185 prefixEnd_7572185 := by exact prefixLift 7572185
  have htrace : WordTrace (prefixWord ++ tailWord_7572185) baseStart_7572185 baseEnd_7572185 := by
    simpa [prefixWord, tailWord_7572185, baseEnd_7572185] using wordTrace_append hprefix tailTrace_7572185
  have hstable : (prefixWord ++ tailWord_7572185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572185).length < 2 ^ (prefixWord ++ tailWord_7572185).sum := by decide
  have hdescent : baseEnd_7572185 < baseStart_7572185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572205 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 6]
def baseStart_7572205 : Nat := 118140960795 + 7572205 * 2 ^ 59
def prefixEnd_7572205 : Nat := 4983230072969 + 3 ^ 40 * 7572205 * 2
def baseEnd_7572205 : Nat := 432020086597627938534841

theorem tailTrace_7572205 : CollatzResearch.WordTrace tailWord_7572205 prefixEnd_7572205 432020086597627938534841 := by
  unfold tailWord_7572205
  simp only [CollatzResearch.WordTrace]
  refine ⟨276181005532201989499838069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184120670354801326333225379 276181005532201989499838069)
  ·
    refine ⟨25891969268643936515609819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276181005532201989499838069 25891969268643936515609819)
    ·
      refine ⟨38837953902965904773414729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25891969268643936515609819 38837953902965904773414729)
      ·
        refine ⟨29128465427224428580061047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38837953902965904773414729 29128465427224428580061047)
        ·
          refine ⟨43692698140836642870091571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29128465427224428580061047 43692698140836642870091571)
          ·
            refine ⟨65539047211254964305137357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43692698140836642870091571 65539047211254964305137357)
            ·
              refine ⟨24577142704220611614426509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65539047211254964305137357 24577142704220611614426509)
              ·
                refine ⟨9216428514082729355409941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24577142704220611614426509 9216428514082729355409941)
                ·
                  refine ⟨432020086597627938534841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9216428514082729355409941 432020086597627938534841)
                  ·
                    rfl

theorem cell23_7572205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_7572205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572205 prefixEnd_7572205 := by exact prefixLift 7572205
  have htrace : WordTrace (prefixWord ++ tailWord_7572205) baseStart_7572205 baseEnd_7572205 := by
    simpa [prefixWord, tailWord_7572205, baseEnd_7572205] using wordTrace_append hprefix tailTrace_7572205
  have hstable : (prefixWord ++ tailWord_7572205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572205).length < 2 ^ (prefixWord ++ tailWord_7572205).sum := by decide
  have hdescent : baseEnd_7572205 < baseStart_7572205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572215 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_7572215 : Nat := 118140960795 + 7572215 * 2 ^ 59
def prefixEnd_7572215 : Nat := 4983230072969 + 3 ^ 40 * 7572215 * 2
def baseEnd_7572215 : Nat := 3888185914185196407688523

theorem tailTrace_7572215 : CollatzResearch.WordTrace tailWord_7572215 prefixEnd_7572215 3888185914185196407688523 := by
  unfold tailWord_7572215
  simp only [CollatzResearch.WordTrace]
  refine ⟨276181370262165761207702099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184120913508110507471801399 276181370262165761207702099)
  ·
    refine ⟨414272055393248641811553149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276181370262165761207702099 414272055393248641811553149)
    ·
      refine ⟨155352020772468240679332431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414272055393248641811553149 155352020772468240679332431)
      ·
        refine ⟨233028031158702361018998647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155352020772468240679332431 233028031158702361018998647)
        ·
          refine ⟨349542046738053541528497971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233028031158702361018998647 349542046738053541528497971)
          ·
            refine ⟨524313070107080312292746957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349542046738053541528497971 524313070107080312292746957)
            ·
              refine ⟨196617401290155117109780109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524313070107080312292746957 196617401290155117109780109)
              ·
                refine ⟨73731525483808168916167541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196617401290155117109780109 73731525483808168916167541)
                ·
                  refine ⟨6912330514107015835890707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73731525483808168916167541 6912330514107015835890707)
                  ·
                    refine ⟨10368495771160523753836061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6912330514107015835890707 10368495771160523753836061)
                    ·
                      refine ⟨3888185914185196407688523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10368495771160523753836061 3888185914185196407688523)
                      ·
                        rfl

theorem cell23_7572215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_7572215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572215 prefixEnd_7572215 := by exact prefixLift 7572215
  have htrace : WordTrace (prefixWord ++ tailWord_7572215) baseStart_7572215 baseEnd_7572215 := by
    simpa [prefixWord, tailWord_7572215, baseEnd_7572215] using wordTrace_append hprefix tailTrace_7572215
  have hstable : (prefixWord ++ tailWord_7572215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572215).length < 2 ^ (prefixWord ++ tailWord_7572215).sum := by decide
  have hdescent : baseEnd_7572215 < baseStart_7572215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572248 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 5, 6]
def baseStart_7572248 : Nat := 118140960795 + 7572248 * 2 ^ 59
def prefixEnd_7572248 : Nat := 4983230072969 + 3 ^ 40 * 7572248 * 2
def baseEnd_7572248 : Nat := 1296067619682264926191957

theorem tailTrace_7572248 : CollatzResearch.WordTrace tailWord_7572248 prefixEnd_7572248 1296067619682264926191957 := by
  unfold tailWord_7572248
  simp only [CollatzResearch.WordTrace]
  refine ⟨138091286935523103921826699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184121715914030805229102265 138091286935523103921826699)
  ·
    refine ⟨207136930403284655882740049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138091286935523103921826699 207136930403284655882740049)
    ·
      refine ⟨155352697802463491912055037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207136930403284655882740049 155352697802463491912055037)
      ·
        refine ⟨58257261675923809467020639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155352697802463491912055037 58257261675923809467020639)
        ·
          refine ⟨87385892513885714200530959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58257261675923809467020639 87385892513885714200530959)
          ·
            refine ⟨131078838770828571300796439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87385892513885714200530959 131078838770828571300796439)
            ·
              refine ⟨196618258156242856951194659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131078838770828571300796439 196618258156242856951194659)
              ·
                refine ⟨294927387234364285426791989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196618258156242856951194659 294927387234364285426791989)
                ·
                  refine ⟨27649442553221651758761749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294927387234364285426791989 27649442553221651758761749)
                  ·
                    refine ⟨1296067619682264926191957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27649442553221651758761749 1296067619682264926191957)
                    ·
                      rfl

theorem cell23_7572248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_7572248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572248 prefixEnd_7572248 := by exact prefixLift 7572248
  have htrace : WordTrace (prefixWord ++ tailWord_7572248) baseStart_7572248 baseEnd_7572248 := by
    simpa [prefixWord, tailWord_7572248, baseEnd_7572248] using wordTrace_append hprefix tailTrace_7572248
  have hstable : (prefixWord ++ tailWord_7572248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572248).length < 2 ^ (prefixWord ++ tailWord_7572248).sum := by decide
  have hdescent : baseEnd_7572248 < baseStart_7572248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572255 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_7572255 : Nat := 118140960795 + 7572255 * 2 ^ 59
def prefixEnd_7572255 : Nat := 4983230072969 + 3 ^ 40 * 7572255 * 2
def baseEnd_7572255 : Nat := 3888206453411376251188339

theorem tailTrace_7572255 : CollatzResearch.WordTrace tailWord_7572255 prefixEnd_7572255 3888206453411376251188339 := by
  unfold tailWord_7572255
  simp only [CollatzResearch.WordTrace]
  refine ⟨276182829182020848039158219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184121886121347232026105479 276182829182020848039158219)
  ·
    refine ⟨414274243773031272058737329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276182829182020848039158219 414274243773031272058737329)
    ·
      refine ⟨310705682829773454044052997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414274243773031272058737329 310705682829773454044052997)
      ·
        refine ⟨58257315530582522633259937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310705682829773454044052997 58257315530582522633259937)
        ·
          refine ⟨43692986647936891974944953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58257315530582522633259937 43692986647936891974944953)
          ·
            refine ⟨32769739985952668981208715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43692986647936891974944953 32769739985952668981208715)
            ·
              refine ⟨49154609978929003471813073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32769739985952668981208715 49154609978929003471813073)
              ·
                refine ⟨36865957484196752603859805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49154609978929003471813073 36865957484196752603859805)
                ·
                  refine ⟨13824734056573782226447427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36865957484196752603859805 13824734056573782226447427)
                  ·
                    refine ⟨20737101084860673339671141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13824734056573782226447427 20737101084860673339671141)
                    ·
                      refine ⟨3888206453411376251188339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20737101084860673339671141 3888206453411376251188339)
                      ·
                        rfl

theorem cell23_7572255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_7572255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572255 prefixEnd_7572255 := by exact prefixLift 7572255
  have htrace : WordTrace (prefixWord ++ tailWord_7572255) baseStart_7572255 baseEnd_7572255 := by
    simpa [prefixWord, tailWord_7572255, baseEnd_7572255] using wordTrace_append hprefix tailTrace_7572255
  have hstable : (prefixWord ++ tailWord_7572255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572255).length < 2 ^ (prefixWord ++ tailWord_7572255).sum := by decide
  have hdescent : baseEnd_7572255 < baseStart_7572255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572266 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7572266 : Nat := 118140960795 + 7572266 * 2 ^ 59
def prefixEnd_7572266 : Nat := 4983230072969 + 3 ^ 40 * 7572266 * 2
def baseEnd_7572266 : Nat := 3888212101698575708150789

theorem tailTrace_7572266 : CollatzResearch.WordTrace tailWord_7572266 prefixEnd_7572266 3888212101698575708150789 := by
  unfold tailWord_7572266
  simp only [CollatzResearch.WordTrace]
  refine ⟨69045807596245249229452163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184122153589987331278539101 69045807596245249229452163)
  ·
    refine ⟨103568711394367873844178245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69045807596245249229452163 103568711394367873844178245)
    ·
      refine ⟨19419133386443976345783421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103568711394367873844178245 19419133386443976345783421)
      ·
        refine ⟨7282175019916491129668783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19419133386443976345783421 7282175019916491129668783)
        ·
          refine ⟨10923262529874736694503175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282175019916491129668783 10923262529874736694503175)
          ·
            refine ⟨16384893794812105041754763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923262529874736694503175 16384893794812105041754763)
            ·
              refine ⟨24577340692218157562632145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16384893794812105041754763 24577340692218157562632145)
              ·
                refine ⟨18433005519163618171974109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24577340692218157562632145 18433005519163618171974109)
                ·
                  refine ⟨6912377069686356814490291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18433005519163618171974109 6912377069686356814490291)
                  ·
                    refine ⟨10368565604529535221735437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6912377069686356814490291 10368565604529535221735437)
                    ·
                      refine ⟨3888212101698575708150789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10368565604529535221735437 3888212101698575708150789)
                      ·
                        rfl

theorem cell23_7572266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7572266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572266 prefixEnd_7572266 := by exact prefixLift 7572266
  have htrace : WordTrace (prefixWord ++ tailWord_7572266) baseStart_7572266 baseEnd_7572266 := by
    simpa [prefixWord, tailWord_7572266, baseEnd_7572266] using wordTrace_append hprefix tailTrace_7572266
  have hstable : (prefixWord ++ tailWord_7572266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572266).length < 2 ^ (prefixWord ++ tailWord_7572266).sum := by decide
  have hdescent : baseEnd_7572266 < baseStart_7572266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572286 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_7572286 : Nat := 118140960795 + 7572286 * 2 ^ 59
def prefixEnd_7572286 : Nat := 4983230072969 + 3 ^ 40 * 7572286 * 2
def baseEnd_7572286 : Nat := 1296074123770555209966899

theorem tailTrace_7572286 : CollatzResearch.WordTrace tailWord_7572286 prefixEnd_7572286 1296074123770555209966899 := by
  unfold tailWord_7572286
  simp only [CollatzResearch.WordTrace]
  refine ⟨34522994980613567541692089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184122639896605693555691141 34522994980613567541692089)
  ·
    refine ⟨25892246235460175656269067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34522994980613567541692089 25892246235460175656269067)
    ·
      refine ⟨38838369353190263484403601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25892246235460175656269067 38838369353190263484403601)
      ·
        refine ⟨29128777014892697613302701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38838369353190263484403601 29128777014892697613302701)
        ·
          refine ⟨10923291380584761604988513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29128777014892697613302701 10923291380584761604988513)
          ·
            refine ⟨8192468535438571203741385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10923291380584761604988513 8192468535438571203741385)
            ·
              refine ⟨6144351401578928402806039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8192468535438571203741385 6144351401578928402806039)
              ·
                refine ⟨9216527102368392604209059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144351401578928402806039 9216527102368392604209059)
                ·
                  refine ⟨13824790653552588906313589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9216527102368392604209059 13824790653552588906313589)
                  ·
                    refine ⟨1296074123770555209966899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13824790653552588906313589 1296074123770555209966899)
                    ·
                      rfl

theorem cell23_7572286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_7572286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572286 prefixEnd_7572286 := by exact prefixLift 7572286
  have htrace : WordTrace (prefixWord ++ tailWord_7572286) baseStart_7572286 baseEnd_7572286 := by
    simpa [prefixWord, tailWord_7572286, baseEnd_7572286] using wordTrace_append hprefix tailTrace_7572286
  have hstable : (prefixWord ++ tailWord_7572286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572286).length < 2 ^ (prefixWord ++ tailWord_7572286).sum := by decide
  have hdescent : baseEnd_7572286 < baseStart_7572286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572306 : List Nat := [3, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_7572306 : Nat := 118140960795 + 7572306 * 2 ^ 59
def prefixEnd_7572306 : Nat := 4983230072969 + 3 ^ 40 * 7572306 * 2
def baseEnd_7572306 : Nat := 3888232640924755551650605

theorem tailTrace_7572306 : CollatzResearch.WordTrace tailWord_7572306 prefixEnd_7572306 3888232640924755551650605 := by
  unfold tailWord_7572306
  simp only [CollatzResearch.WordTrace]
  refine ⟨69046172326209020937316193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184123126203224055832843181 69046172326209020937316193)
  ·
    refine ⟨51784629244656765702987145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69046172326209020937316193 51784629244656765702987145)
    ·
      refine ⟨38838471933492574277240359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51784629244656765702987145 38838471933492574277240359)
      ·
        refine ⟨58257707900238861415860539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38838471933492574277240359 58257707900238861415860539)
        ·
          refine ⟨87386561850358292123790809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58257707900238861415860539 87386561850358292123790809)
          ·
            refine ⟨65539921387768719092843107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87386561850358292123790809 65539921387768719092843107)
            ·
              refine ⟨98309882081653078639264661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65539921387768719092843107 98309882081653078639264661)
              ·
                refine ⟨4608275722577488061215531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98309882081653078639264661 4608275722577488061215531)
                ·
                  refine ⟨6912413583866232091823297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608275722577488061215531 6912413583866232091823297)
                  ·
                    refine ⟨5184310187899674068867473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6912413583866232091823297 5184310187899674068867473)
                    ·
                      refine ⟨3888232640924755551650605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184310187899674068867473 3888232640924755551650605)
                      ·
                        rfl

theorem cell23_7572306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_7572306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572306 prefixEnd_7572306 := by exact prefixLift 7572306
  have htrace : WordTrace (prefixWord ++ tailWord_7572306) baseStart_7572306 baseEnd_7572306 := by
    simpa [prefixWord, tailWord_7572306, baseEnd_7572306] using wordTrace_append hprefix tailTrace_7572306
  have hstable : (prefixWord ++ tailWord_7572306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572306).length < 2 ^ (prefixWord ++ tailWord_7572306).sum := by decide
  have hdescent : baseEnd_7572306 < baseStart_7572306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572316 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_7572316 : Nat := 118140960795 + 7572316 * 2 ^ 59
def prefixEnd_7572316 : Nat := 4983230072969 + 3 ^ 40 * 7572316 * 2
def baseEnd_7572316 : Nat := 1296079258577100170841853

theorem tailTrace_7572316 : CollatzResearch.WordTrace tailWord_7572316 prefixEnd_7572316 1296079258577100170841853 := by
  unfold tailWord_7572316
  simp only [CollatzResearch.WordTrace]
  refine ⟨138092527017399927728564401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184123369356533236971419201 138092527017399927728564401)
  ·
    refine ⟨103569395263049945796423301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138092527017399927728564401 103569395263049945796423301)
    ·
      refine ⟨19419261611821864836829369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103569395263049945796423301 19419261611821864836829369)
      ·
        refine ⟨14564446208866398627622027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19419261611821864836829369 14564446208866398627622027)
        ·
          refine ⟨21846669313299597941433041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14564446208866398627622027 21846669313299597941433041)
          ·
            refine ⟨16385001984974698456074781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21846669313299597941433041 16385001984974698456074781)
            ·
              refine ⟨6144375744365511921028043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16385001984974698456074781 6144375744365511921028043)
              ·
                refine ⟨9216563616548267881542065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144375744365511921028043 9216563616548267881542065)
                ·
                  refine ⟨6912422712411200911156549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9216563616548267881542065 6912422712411200911156549)
                  ·
                    refine ⟨1296079258577100170841853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6912422712411200911156549 1296079258577100170841853)
                    ·
                      rfl

theorem cell23_7572316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_7572316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572316 prefixEnd_7572316 := by exact prefixLift 7572316
  have htrace : WordTrace (prefixWord ++ tailWord_7572316) baseStart_7572316 baseEnd_7572316 := by
    simpa [prefixWord, tailWord_7572316, baseEnd_7572316] using wordTrace_append hprefix tailTrace_7572316
  have hstable : (prefixWord ++ tailWord_7572316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572316).length < 2 ^ (prefixWord ++ tailWord_7572316).sum := by decide
  have hdescent : baseEnd_7572316 < baseStart_7572316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572349 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_7572349 : Nat := 118140960795 + 7572349 * 2 ^ 59
def prefixEnd_7572349 : Nat := 4983230072969 + 3 ^ 40 * 7572349 * 2
def baseEnd_7572349 : Nat := 3888254720592898883412907

theorem tailTrace_7572349 : CollatzResearch.WordTrace tailWord_7572349 prefixEnd_7572349 3888254720592898883412907 := by
  unfold tailWord_7572349
  simp only [CollatzResearch.WordTrace]
  refine ⟨276186257643680302093080101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184124171762453534728720067 276186257643680302093080101)
  ·
    refine ⟨51784923308190056642452519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276186257643680302093080101 51784923308190056642452519)
    ·
      refine ⟨77677384962285084963678779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51784923308190056642452519 77677384962285084963678779)
      ·
        refine ⟨116516077443427627445518169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77677384962285084963678779 116516077443427627445518169)
        ·
          refine ⟨87387058082570720584138627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116516077443427627445518169 87387058082570720584138627)
          ·
            refine ⟨131080587123856080876207941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87387058082570720584138627 131080587123856080876207941)
            ·
              refine ⟨24577610085723015164288989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131080587123856080876207941 24577610085723015164288989)
              ·
                refine ⟨9216603782146130686608371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24577610085723015164288989 9216603782146130686608371)
                ·
                  refine ⟨13824905673219196029912557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9216603782146130686608371 13824905673219196029912557)
                  ·
                    refine ⟨5184339627457198511217209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13824905673219196029912557 5184339627457198511217209)
                    ·
                      refine ⟨3888254720592898883412907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184339627457198511217209 3888254720592898883412907)
                      ·
                        rfl

theorem cell23_7572349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_7572349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572349 prefixEnd_7572349 := by exact prefixLift 7572349
  have htrace : WordTrace (prefixWord ++ tailWord_7572349) baseStart_7572349 baseEnd_7572349 := by
    simpa [prefixWord, tailWord_7572349, baseEnd_7572349] using wordTrace_append hprefix tailTrace_7572349
  have hstable : (prefixWord ++ tailWord_7572349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572349).length < 2 ^ (prefixWord ++ tailWord_7572349).sum := by decide
  have hdescent : baseEnd_7572349 < baseStart_7572349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572375 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_7572375 : Nat := 118140960795 + 7572375 * 2 ^ 59
def prefixEnd_7572375 : Nat := 4983230072969 + 3 ^ 40 * 7572375 * 2
def baseEnd_7572375 : Nat := 3888268071089915781687787

theorem tailTrace_7572375 : CollatzResearch.WordTrace tailWord_7572375 prefixEnd_7572375 3888268071089915781687787 := by
  unfold tailWord_7572375
  simp only [CollatzResearch.WordTrace]
  refine ⟨276187205941586108533526579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184124803961057405689017719 276187205941586108533526579)
  ·
    refine ⟨414280808912379162800289869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276187205941586108533526579 414280808912379162800289869)
    ·
      refine ⟨155355303342142186050108701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414280808912379162800289869 155355303342142186050108701)
      ·
        refine ⟨58258238753303319768790763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155355303342142186050108701 58258238753303319768790763)
        ·
          refine ⟨87387358129954979653186145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58258238753303319768790763 87387358129954979653186145)
          ·
            refine ⟨65540518597466234739889609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87387358129954979653186145 65540518597466234739889609)
            ·
              refine ⟨49155388948099676054917207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65540518597466234739889609 49155388948099676054917207)
              ·
                refine ⟨73733083422149514082375811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49155388948099676054917207 73733083422149514082375811)
                ·
                  refine ⟨110599625133224271123563717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73733083422149514082375811 110599625133224271123563717)
                  ·
                    refine ⟨20737429712479550835668197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110599625133224271123563717 20737429712479550835668197)
                    ·
                      refine ⟨3888268071089915781687787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20737429712479550835668197 3888268071089915781687787)
                      ·
                        rfl

theorem cell23_7572375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_7572375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572375 prefixEnd_7572375 := by exact prefixLift 7572375
  have htrace : WordTrace (prefixWord ++ tailWord_7572375) baseStart_7572375 baseEnd_7572375 := by
    simpa [prefixWord, tailWord_7572375, baseEnd_7572375] using wordTrace_append hprefix tailTrace_7572375
  have hstable : (prefixWord ++ tailWord_7572375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572375).length < 2 ^ (prefixWord ++ tailWord_7572375).sum := by decide
  have hdescent : baseEnd_7572375 < baseStart_7572375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572395 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 3]
def baseStart_7572395 : Nat := 118140960795 + 7572395 * 2 ^ 59
def prefixEnd_7572395 : Nat := 4983230072969 + 3 ^ 40 * 7572395 * 2
def baseEnd_7572395 : Nat := 3888278340703005703437695

theorem tailTrace_7572395 : CollatzResearch.WordTrace tailWord_7572395 prefixEnd_7572395 3888278340703005703437695 := by
  unfold tailWord_7572395
  simp only [CollatzResearch.WordTrace]
  refine ⟨276187935401513651949254639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184125290267675767966169759 276187935401513651949254639)
  ·
    refine ⟨414281903102270477923881959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276187935401513651949254639 414281903102270477923881959)
    ·
      refine ⟨621422854653405716885822939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414281903102270477923881959 621422854653405716885822939)
      ·
        refine ⟨932134281980108575328734409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621422854653405716885822939 932134281980108575328734409)
        ·
          refine ⟨699100711485081431496550807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932134281980108575328734409 699100711485081431496550807)
          ·
            refine ⟨1048651067227622147244826211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699100711485081431496550807 1048651067227622147244826211)
            ·
              refine ⟨1572976600841433220867239317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1048651067227622147244826211 1572976600841433220867239317)
              ·
                refine ⟨73733278164442182228151843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1572976600841433220867239317 73733278164442182228151843)
                ·
                  refine ⟨110599917246663273342227765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73733278164442182228151843 110599917246663273342227765)
                  ·
                    refine ⟨10368742241874681875833853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110599917246663273342227765 10368742241874681875833853)
                    ·
                      refine ⟨3888278340703005703437695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10368742241874681875833853 3888278340703005703437695)
                      ·
                        rfl

theorem cell23_7572395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 3].length) (baseStart_7572395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572395 prefixEnd_7572395 := by exact prefixLift 7572395
  have htrace : WordTrace (prefixWord ++ tailWord_7572395) baseStart_7572395 baseEnd_7572395 := by
    simpa [prefixWord, tailWord_7572395, baseEnd_7572395] using wordTrace_append hprefix tailTrace_7572395
  have hstable : (prefixWord ++ tailWord_7572395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572395).length < 2 ^ (prefixWord ++ tailWord_7572395).sum := by decide
  have hdescent : baseEnd_7572395 < baseStart_7572395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572413 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_7572413 : Nat := 118140960795 + 7572413 * 2 ^ 59
def prefixEnd_7572413 : Nat := 4983230072969 + 3 ^ 40 * 7572413 * 2
def baseEnd_7572413 : Nat := 3888287583354786633012613

theorem tailTrace_7572413 : CollatzResearch.WordTrace tailWord_7572413 prefixEnd_7572413 3888287583354786633012613 := by
  unfold tailWord_7572413
  simp only [CollatzResearch.WordTrace]
  refine ⟨276188591915448441023409893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184125727943632294015606595 276188591915448441023409893)
  ·
    refine ⟨51785360984146582691889355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276188591915448441023409893 51785360984146582691889355)
    ·
      refine ⟨77678041476219874037834033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51785360984146582691889355 77678041476219874037834033)
      ·
        refine ⟨58258531107164905528375525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77678041476219874037834033 58258531107164905528375525)
        ·
          refine ⟨10923474582593419786570411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58258531107164905528375525 10923474582593419786570411)
          ·
            refine ⟨16385211873890129679855617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923474582593419786570411 16385211873890129679855617)
            ·
              refine ⟨12288908905417597259891713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16385211873890129679855617 12288908905417597259891713)
              ·
                refine ⟨9216681679063197944918785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12288908905417597259891713 9216681679063197944918785)
                ·
                  refine ⟨6912511259297398458689089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9216681679063197944918785 6912511259297398458689089)
                  ·
                    refine ⟨5184383444473048844016817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6912511259297398458689089 5184383444473048844016817)
                    ·
                      refine ⟨3888287583354786633012613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184383444473048844016817 3888287583354786633012613)
                      ·
                        rfl

theorem cell23_7572413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_7572413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572413 prefixEnd_7572413 := by exact prefixLift 7572413
  have htrace : WordTrace (prefixWord ++ tailWord_7572413) baseStart_7572413 baseEnd_7572413 := by
    simpa [prefixWord, tailWord_7572413, baseEnd_7572413] using wordTrace_append hprefix tailTrace_7572413
  have hstable : (prefixWord ++ tailWord_7572413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572413).length < 2 ^ (prefixWord ++ tailWord_7572413).sum := by decide
  have hdescent : baseEnd_7572413 < baseStart_7572413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572415 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 4, 5]
def baseStart_7572415 : Nat := 118140960795 + 7572415 * 2 ^ 59
def prefixEnd_7572415 : Nat := 4983230072969 + 3 ^ 40 * 7572415 * 2
def baseEnd_7572415 : Nat := 1296096203438698541729201

theorem tailTrace_7572415 : CollatzResearch.WordTrace tailWord_7572415 prefixEnd_7572415 1296096203438698541729201 := by
  unfold tailWord_7572415
  simp only [CollatzResearch.WordTrace]
  refine ⟨276188664861441195364982699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184125776574294130243321799 276188664861441195364982699)
  ·
    refine ⟨414282997292161793047474049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276188664861441195364982699 414282997292161793047474049)
    ·
      refine ⟨310712247969121344785605537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414282997292161793047474049 310712247969121344785605537)
      ·
        refine ⟨233034185976841008589204153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310712247969121344785605537 233034185976841008589204153)
        ·
          refine ⟨174775639482630756441903115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233034185976841008589204153 174775639482630756441903115)
          ·
            refine ⟨262163459223946134662854673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174775639482630756441903115 262163459223946134662854673)
            ·
              refine ⟨196622594417959600997141005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262163459223946134662854673 196622594417959600997141005)
              ·
                refine ⟨73733472906734850373927877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196622594417959600997141005 73733472906734850373927877)
                ·
                  refine ⟨13825026170012784445111477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73733472906734850373927877 13825026170012784445111477)
                  ·
                    refine ⟨1296096203438698541729201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13825026170012784445111477 1296096203438698541729201)
                    ·
                      rfl

theorem cell23_7572415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_7572415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572415 prefixEnd_7572415 := by exact prefixLift 7572415
  have htrace : WordTrace (prefixWord ++ tailWord_7572415) baseStart_7572415 baseEnd_7572415 := by
    simpa [prefixWord, tailWord_7572415, baseEnd_7572415] using wordTrace_append hprefix tailTrace_7572415
  have hstable : (prefixWord ++ tailWord_7572415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572415).length < 2 ^ (prefixWord ++ tailWord_7572415).sum := by decide
  have hdescent : baseEnd_7572415 < baseStart_7572415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572452 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_7572452 : Nat := 118140960795 + 7572452 * 2 ^ 59
def prefixEnd_7572452 : Nat := 4983230072969 + 3 ^ 40 * 7572452 * 2
def baseEnd_7572452 : Nat := 3888307609100311980424933

theorem tailTrace_7572452 : CollatzResearch.WordTrace tailWord_7572452 prefixEnd_7572452 3888307609100311980424933 := by
  unfold tailWord_7572452
  simp only [CollatzResearch.WordTrace]
  refine ⟨138095007181153575342039805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184126676241538100456053073 138095007181153575342039805)
  ·
    refine ⟨51785627692932590753264927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138095007181153575342039805 51785627692932590753264927)
    ·
      refine ⟨77678441539398886129897391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51785627692932590753264927 77678441539398886129897391)
      ·
        refine ⟨116517662309098329194846087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77678441539398886129897391 116517662309098329194846087)
        ·
          refine ⟨174776493463647493792269131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116517662309098329194846087 174776493463647493792269131)
          ·
            refine ⟨262164740195471240688403697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174776493463647493792269131 262164740195471240688403697)
            ·
              refine ⟨196623555146603430516302773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262164740195471240688403697 196623555146603430516302773)
              ·
                refine ⟨18433458294994071610903385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196623555146603430516302773 18433458294994071610903385)
                ·
                  refine ⟨13825093721245553708177539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18433458294994071610903385 13825093721245553708177539)
                  ·
                    refine ⟨20737640581868330562266309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13825093721245553708177539 20737640581868330562266309)
                    ·
                      refine ⟨3888307609100311980424933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20737640581868330562266309 3888307609100311980424933)
                      ·
                        rfl

theorem cell23_7572452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_7572452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572452 prefixEnd_7572452 := by exact prefixLift 7572452
  have htrace : WordTrace (prefixWord ++ tailWord_7572452) baseStart_7572452 baseEnd_7572452 := by
    simpa [prefixWord, tailWord_7572452, baseEnd_7572452] using wordTrace_append hprefix tailTrace_7572452
  have hstable : (prefixWord ++ tailWord_7572452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572452).length < 2 ^ (prefixWord ++ tailWord_7572452).sum := by decide
  have hdescent : baseEnd_7572452 < baseStart_7572452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572472 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_7572472 : Nat := 118140960795 + 7572472 * 2 ^ 59
def prefixEnd_7572472 : Nat := 4983230072969 + 3 ^ 40 * 7572472 * 2
def baseEnd_7572472 : Nat := 3888317878713401902174841

theorem tailTrace_7572472 : CollatzResearch.WordTrace tailWord_7572472 prefixEnd_7572472 3888317878713401902174841 := by
  unfold tailWord_7572472
  simp only [CollatzResearch.WordTrace]
  refine ⟨138095371911117347049903835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184127162548156462733205113 138095371911117347049903835)
  ·
    refine ⟨207143057866676020574855753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138095371911117347049903835 207143057866676020574855753)
    ·
      refine ⟨155357293400007015431141815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207143057866676020574855753 155357293400007015431141815)
      ·
        refine ⟨233035940100010523146712723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155357293400007015431141815 233035940100010523146712723)
        ·
          refine ⟨349553910150015784720069085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233035940100010523146712723 349553910150015784720069085)
          ·
            refine ⟨131082716306255919270025907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349553910150015784720069085 131082716306255919270025907)
            ·
              refine ⟨196624074459383878905038861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131082716306255919270025907 196624074459383878905038861)
              ·
                refine ⟨73734027922268954589389573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196624074459383878905038861 73734027922268954589389573)
                ·
                  refine ⟨13825130235425428985510545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73734027922268954589389573 13825130235425428985510545)
                  ·
                    refine ⟨10368847676569071739132909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13825130235425428985510545 10368847676569071739132909)
                    ·
                      refine ⟨3888317878713401902174841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10368847676569071739132909 3888317878713401902174841)
                      ·
                        rfl

theorem cell23_7572472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_7572472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572472 prefixEnd_7572472 := by exact prefixLift 7572472
  have htrace : WordTrace (prefixWord ++ tailWord_7572472) baseStart_7572472 baseEnd_7572472 := by
    simpa [prefixWord, tailWord_7572472, baseEnd_7572472] using wordTrace_append hprefix tailTrace_7572472
  have hstable : (prefixWord ++ tailWord_7572472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572472).length < 2 ^ (prefixWord ++ tailWord_7572472).sum := by decide
  have hdescent : baseEnd_7572472 < baseStart_7572472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572513 : List Nat := [1, 2, 3, 2, 3, 3, 1, 3, 1, 4]
def baseStart_7572513 : Nat := 118140960795 + 7572513 * 2 ^ 59
def prefixEnd_7572513 : Nat := 4983230072969 + 3 ^ 40 * 7572513 * 2
def baseEnd_7572513 : Nat := 1296112977140078747254051

theorem tailTrace_7572513 : CollatzResearch.WordTrace tailWord_7572513 prefixEnd_7572513 1296112977140078747254051 := by
  unfold tailWord_7572513
  simp only [CollatzResearch.WordTrace]
  refine ⟨276192239215086158102050193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184128159476724105401366795 276192239215086158102050193)
  ·
    refine ⟨207144179411314618576537645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276192239215086158102050193 207144179411314618576537645)
    ·
      refine ⟨77679067279242981966201617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207144179411314618576537645 77679067279242981966201617)
      ·
        refine ⟨58259300459432236474651213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77679067279242981966201617 58259300459432236474651213)
        ·
          refine ⟨21847237672287088677994205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58259300459432236474651213 21847237672287088677994205)
          ·
            refine ⟨8192714127107658254247827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21847237672287088677994205 8192714127107658254247827)
            ·
              refine ⟨12289071190661487381371741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8192714127107658254247827 12289071190661487381371741)
              ·
                refine ⟨4608401696498057768014403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12289071190661487381371741 4608401696498057768014403)
                ·
                  refine ⟨6912602544747086652021605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608401696498057768014403 6912602544747086652021605)
                  ·
                    refine ⟨1296112977140078747254051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6912602544747086652021605 1296112977140078747254051)
                    ·
                      rfl

theorem cell23_7572513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_7572513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572513 prefixEnd_7572513 := by exact prefixLift 7572513
  have htrace : WordTrace (prefixWord ++ tailWord_7572513) baseStart_7572513 baseEnd_7572513 := by
    simpa [prefixWord, tailWord_7572513, baseEnd_7572513] using wordTrace_append hprefix tailTrace_7572513
  have hstable : (prefixWord ++ tailWord_7572513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572513).length < 2 ^ (prefixWord ++ tailWord_7572513).sum := by decide
  have hdescent : baseEnd_7572513 < baseStart_7572513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572536 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_7572536 : Nat := 118140960795 + 7572536 * 2 ^ 59
def prefixEnd_7572536 : Nat := 4983230072969 + 3 ^ 40 * 7572536 * 2
def baseEnd_7572536 : Nat := 3888350741475289651774547

theorem tailTrace_7572536 : CollatzResearch.WordTrace tailWord_7572536 prefixEnd_7572536 3888350741475289651774547 := by
  unfold tailWord_7572536
  simp only [CollatzResearch.WordTrace]
  refine ⟨138096539047001416515068731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184128718729335222020091641 138096539047001416515068731)
  ·
    refine ⟨207144808570502124772603097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138096539047001416515068731 207144808570502124772603097)
    ·
      refine ⟨155358606427876593579452323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207144808570502124772603097 155358606427876593579452323)
      ·
        refine ⟨233037909641814890369178485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155358606427876593579452323 233037909641814890369178485)
        ·
          refine ⟨21847304028920145972110483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233037909641814890369178485 21847304028920145972110483)
          ·
            refine ⟨32770956043380218958165725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21847304028920145972110483 32770956043380218958165725)
            ·
              refine ⟨12289108516267582109312147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32770956043380218958165725 12289108516267582109312147)
              ·
                refine ⟨18433662774401373163968221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12289108516267582109312147 18433662774401373163968221)
                ·
                  refine ⟨6912623540400514936488083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18433662774401373163968221 6912623540400514936488083)
                  ·
                    refine ⟨10368935310600772404732125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6912623540400514936488083 10368935310600772404732125)
                    ·
                      refine ⟨3888350741475289651774547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10368935310600772404732125 3888350741475289651774547)
                      ·
                        rfl

theorem cell23_7572536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_7572536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572536 prefixEnd_7572536 := by exact prefixLift 7572536
  have htrace : WordTrace (prefixWord ++ tailWord_7572536) baseStart_7572536 baseEnd_7572536 := by
    simpa [prefixWord, tailWord_7572536, baseEnd_7572536] using wordTrace_append hprefix tailTrace_7572536
  have hstable : (prefixWord ++ tailWord_7572536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572536).length < 2 ^ (prefixWord ++ tailWord_7572536).sum := by decide
  have hdescent : baseEnd_7572536 < baseStart_7572536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572552 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 1, 6]
def baseStart_7572552 : Nat := 118140960795 + 7572552 * 2 ^ 59
def prefixEnd_7572552 : Nat := 4983230072969 + 3 ^ 40 * 7572552 * 2
def baseEnd_7572552 : Nat := 1296119652388587196391491

theorem tailTrace_7572552 : CollatzResearch.WordTrace tailWord_7572552 prefixEnd_7572552 1296119652388587196391491 := by
  unfold tailWord_7572552
  simp only [CollatzResearch.WordTrace]
  refine ⟨138096830830972433881359955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184129107774629911841813273 138096830830972433881359955)
  ·
    refine ⟨207145246246458650822039933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138096830830972433881359955 207145246246458650822039933)
    ·
      refine ⟨77679467342421994058264975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207145246246458650822039933 77679467342421994058264975)
      ·
        refine ⟨116519201013632991087397463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77679467342421994058264975 116519201013632991087397463)
        ·
          refine ⟨174778801520449486631096195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116519201013632991087397463 174778801520449486631096195)
          ·
            refine ⟨262168202280674229946644293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174778801520449486631096195 262168202280674229946644293)
            ·
              refine ⟨49156537927626418114995805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262168202280674229946644293 49156537927626418114995805)
              ·
                refine ⟨18433701722859906793123427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49156537927626418114995805 18433701722859906793123427)
                ·
                  refine ⟨27650552584289860189685141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18433701722859906793123427 27650552584289860189685141)
                  ·
                    refine ⟨1296119652388587196391491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27650552584289860189685141 1296119652388587196391491)
                    ·
                      rfl

theorem cell23_7572552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_7572552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572552 prefixEnd_7572552 := by exact prefixLift 7572552
  have htrace : WordTrace (prefixWord ++ tailWord_7572552) baseStart_7572552 baseEnd_7572552 := by
    simpa [prefixWord, tailWord_7572552, baseEnd_7572552] using wordTrace_append hprefix tailTrace_7572552
  have hstable : (prefixWord ++ tailWord_7572552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572552).length < 2 ^ (prefixWord ++ tailWord_7572552).sum := by decide
  have hdescent : baseEnd_7572552 < baseStart_7572552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572576 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 1, 1, 4]
def baseStart_7572576 : Nat := 118140960795 + 7572576 * 2 ^ 59
def prefixEnd_7572576 : Nat := 4983230072969 + 3 ^ 40 * 7572576 * 2
def baseEnd_7572576 : Nat := 3888371280701469495274363

theorem tailTrace_7572576 : CollatzResearch.WordTrace tailWord_7572576 prefixEnd_7572576 3888371280701469495274363 := by
  unfold tailWord_7572576
  simp only [CollatzResearch.WordTrace]
  refine ⟨138097268506928959930796791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184129691342571946574395721 138097268506928959930796791)
  ·
    refine ⟨207145902760393439896195187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138097268506928959930796791 207145902760393439896195187)
    ·
      refine ⟨310718854140590159844292781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207145902760393439896195187 310718854140590159844292781)
      ·
        refine ⟨116519570302721309941609793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310718854140590159844292781 116519570302721309941609793)
        ·
          refine ⟨87389677727040982456207345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116519570302721309941609793 87389677727040982456207345)
          ·
            refine ⟨65542258295280736842155509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87389677727040982456207345 65542258295280736842155509)
            ·
              refine ⟨6144586715182569078952079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65542258295280736842155509 6144586715182569078952079)
              ·
                refine ⟨9216880072773853618428119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144586715182569078952079 9216880072773853618428119)
                ·
                  refine ⟨13825320109160780427642179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9216880072773853618428119 13825320109160780427642179)
                  ·
                    refine ⟨20737980163741170641463269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13825320109160780427642179 20737980163741170641463269)
                    ·
                      refine ⟨3888371280701469495274363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20737980163741170641463269 3888371280701469495274363)
                      ·
                        rfl

theorem cell23_7572576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_7572576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572576 prefixEnd_7572576 := by exact prefixLift 7572576
  have htrace : WordTrace (prefixWord ++ tailWord_7572576) baseStart_7572576 baseEnd_7572576 := by
    simpa [prefixWord, tailWord_7572576, baseEnd_7572576] using wordTrace_append hprefix tailTrace_7572576
  have hstable : (prefixWord ++ tailWord_7572576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572576).length < 2 ^ (prefixWord ++ tailWord_7572576).sum := by decide
  have hdescent : baseEnd_7572576 < baseStart_7572576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572586 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_7572586 : Nat := 118140960795 + 7572586 * 2 ^ 59
def prefixEnd_7572586 : Nat := 4983230072969 + 3 ^ 40 * 7572586 * 2
def baseEnd_7572586 : Nat := 1296125471836004818716439

theorem tailTrace_7572586 : CollatzResearch.WordTrace tailWord_7572586 prefixEnd_7572586 1296125471836004818716439 := by
  unfold tailWord_7572586
  simp only [CollatzResearch.WordTrace]
  refine ⟨69048725435955422892364403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184129934495881127712971741 69048725435955422892364403)
  ·
    refine ⟨103573088153933134338546605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69048725435955422892364403 103573088153933134338546605)
    ·
      refine ⟨38839908057724925376954977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103573088153933134338546605 38839908057724925376954977)
      ·
        refine ⟨29129931043293694032716233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38839908057724925376954977 29129931043293694032716233)
        ·
          refine ⟨21847448282470270524537175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29129931043293694032716233 21847448282470270524537175)
          ·
            refine ⟨32771172423705405786805763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21847448282470270524537175 32771172423705405786805763)
            ·
              refine ⟨49156758635558108680208645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32771172423705405786805763 49156758635558108680208645)
              ·
                refine ⟨9216892244167145377539121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49156758635558108680208645 9216892244167145377539121)
                ·
                  refine ⟨6912669183125359033154341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9216892244167145377539121 6912669183125359033154341)
                  ·
                    refine ⟨1296125471836004818716439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6912669183125359033154341 1296125471836004818716439)
                    ·
                      rfl

theorem cell23_7572586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_7572586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572586 prefixEnd_7572586 := by exact prefixLift 7572586
  have htrace : WordTrace (prefixWord ++ tailWord_7572586) baseStart_7572586 baseEnd_7572586 := by
    simpa [prefixWord, tailWord_7572586, baseEnd_7572586] using wordTrace_append hprefix tailTrace_7572586
  have hstable : (prefixWord ++ tailWord_7572586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572586).length < 2 ^ (prefixWord ++ tailWord_7572586).sum := by decide
  have hdescent : baseEnd_7572586 < baseStart_7572586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572616 : List Nat := [2, 1, 3, 4, 2, 1, 3, 7]
def baseStart_7572616 : Nat := 118140960795 + 7572616 * 2 ^ 59
def prefixEnd_7572616 : Nat := 4983230072969 + 3 ^ 40 * 7572616 * 2
def baseEnd_7572616 : Nat := 144014511849172197732377

theorem tailTrace_7572616 : CollatzResearch.WordTrace tailWord_7572616 prefixEnd_7572616 144014511849172197732377 := by
  unfold tailWord_7572616
  simp only [CollatzResearch.WordTrace]
  refine ⟨138097997966856503346524851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184130663955808671128699801 138097997966856503346524851)
  ·
    refine ⟨207146996950284755019787277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138097997966856503346524851 207146996950284755019787277)
    ·
      refine ⟨77680123856356783132420229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207146996950284755019787277 77680123856356783132420229)
      ·
        refine ⟨14565023223066896837328793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77680123856356783132420229 14565023223066896837328793)
        ·
          refine ⟨10923767417300172627996595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14565023223066896837328793 10923767417300172627996595)
          ·
            refine ⟨16385651125950258941994893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923767417300172627996595 16385651125950258941994893)
            ·
              refine ⟨6144619172231347103248085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16385651125950258941994893 6144619172231347103248085)
              ·
                refine ⟨144014511849172197732377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6144619172231347103248085 144014511849172197732377)
                ·
                  rfl

theorem cell23_7572616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 7].length) (baseStart_7572616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572616 prefixEnd_7572616 := by exact prefixLift 7572616
  have htrace : WordTrace (prefixWord ++ tailWord_7572616) baseStart_7572616 baseEnd_7572616 := by
    simpa [prefixWord, tailWord_7572616, baseEnd_7572616] using wordTrace_append hprefix tailTrace_7572616
  have hstable : (prefixWord ++ tailWord_7572616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572616).length < 2 ^ (prefixWord ++ tailWord_7572616).sum := by decide
  have hdescent : baseEnd_7572616 < baseStart_7572616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572626 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_7572626 : Nat := 118140960795 + 7572626 * 2 ^ 59
def prefixEnd_7572626 : Nat := 4983230072969 + 3 ^ 40 * 7572626 * 2
def baseEnd_7572626 : Nat := 3888396954734194299649133

theorem tailTrace_7572626 : CollatzResearch.WordTrace tailWord_7572626 prefixEnd_7572626 3888396954734194299649133 := by
  unfold tailWord_7572626
  simp only [CollatzResearch.WordTrace]
  refine ⟨69049090165919194600228433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184130907109117852267275821 69049090165919194600228433)
  ·
    refine ⟨51786817624439395950171325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69049090165919194600228433 51786817624439395950171325)
    ·
      refine ⟨19420056609164773481314247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51786817624439395950171325 19420056609164773481314247)
      ·
        refine ⟨29130084913747160221971371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19420056609164773481314247 29130084913747160221971371)
        ·
          refine ⟨43695127370620740332957057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29130084913747160221971371 43695127370620740332957057)
          ·
            refine ⟨32771345527965555249717793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43695127370620740332957057 32771345527965555249717793)
            ·
              refine ⟨24578509145974166437288345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32771345527965555249717793 24578509145974166437288345)
              ·
                refine ⟨18433881859480624827966259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24578509145974166437288345 18433881859480624827966259)
                ·
                  refine ⟨27650822789220937241949389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18433881859480624827966259 27650822789220937241949389)
                  ·
                    refine ⟨10369058545957851465731021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27650822789220937241949389 10369058545957851465731021)
                    ·
                      refine ⟨3888396954734194299649133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369058545957851465731021 3888396954734194299649133)
                      ·
                        rfl

theorem cell23_7572626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_7572626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572626 prefixEnd_7572626 := by exact prefixLift 7572626
  have htrace : WordTrace (prefixWord ++ tailWord_7572626) baseStart_7572626 baseEnd_7572626 := by
    simpa [prefixWord, tailWord_7572626, baseEnd_7572626] using wordTrace_append hprefix tailTrace_7572626
  have hstable : (prefixWord ++ tailWord_7572626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572626).length < 2 ^ (prefixWord ++ tailWord_7572626).sum := by decide
  have hdescent : baseEnd_7572626 < baseStart_7572626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572652 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_7572652 : Nat := 118140960795 + 7572652 * 2 ^ 59
def prefixEnd_7572652 : Nat := 4983230072969 + 3 ^ 40 * 7572652 * 2
def baseEnd_7572652 : Nat := 3888410305231211197924013

theorem tailTrace_7572652 : CollatzResearch.WordTrace tailWord_7572652 prefixEnd_7572652 3888410305231211197924013 := by
  unfold tailWord_7572652
  simp only [CollatzResearch.WordTrace]
  refine ⟨138098654480791292420680105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184131539307721723227573473 138098654480791292420680105)
  ·
    refine ⟨103573990860593469315510079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138098654480791292420680105 103573990860593469315510079)
    ·
      refine ⟨155360986290890203973265119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103573990860593469315510079 155360986290890203973265119)
      ·
        refine ⟨233041479436335305959897679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155360986290890203973265119 233041479436335305959897679)
        ·
          refine ⟨349562219154502958939846519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233041479436335305959897679 349562219154502958939846519)
          ·
            refine ⟨524343328731754438409769779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349562219154502958939846519 524343328731754438409769779)
            ·
              refine ⟨786514993097631657614654669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524343328731754438409769779 786514993097631657614654669)
              ·
                refine ⟨294943122411611871605495501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 786514993097631657614654669 294943122411611871605495501)
                ·
                  refine ⟨110603670904354451852060813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294943122411611871605495501 110603670904354451852060813)
                  ·
                    refine ⟨41476376589132919444522805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110603670904354451852060813 41476376589132919444522805)
                    ·
                      refine ⟨3888410305231211197924013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41476376589132919444522805 3888410305231211197924013)
                      ·
                        rfl

theorem cell23_7572652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_7572652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572652 prefixEnd_7572652 := by exact prefixLift 7572652
  have htrace : WordTrace (prefixWord ++ tailWord_7572652) baseStart_7572652 baseEnd_7572652 := by
    simpa [prefixWord, tailWord_7572652, baseEnd_7572652] using wordTrace_append hprefix tailTrace_7572652
  have hstable : (prefixWord ++ tailWord_7572652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572652).length < 2 ^ (prefixWord ++ tailWord_7572652).sum := by decide
  have hdescent : baseEnd_7572652 < baseStart_7572652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572669 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_7572669 : Nat := 118140960795 + 7572669 * 2 ^ 59
def prefixEnd_7572669 : Nat := 4983230072969 + 3 ^ 40 * 7572669 * 2
def baseEnd_7572669 : Nat := 3888419034402337631411435

theorem tailTrace_7572669 : CollatzResearch.WordTrace tailWord_7572669 prefixEnd_7572669 3888419034402337631411435 := by
  unfold tailWord_7572669
  simp only [CollatzResearch.WordTrace]
  refine ⟨276197929002520996744729061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184131952668347331163152707 276197929002520996744729061)
  ·
    refine ⟨51787111687972686889636699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276197929002520996744729061 51787111687972686889636699)
    ·
      refine ⟨77680667531959030334455049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51787111687972686889636699 77680667531959030334455049)
      ·
        refine ⟨58260500648969272750841287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77680667531959030334455049 58260500648969272750841287)
        ·
          refine ⟨87390750973453909126261931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58260500648969272750841287 87390750973453909126261931)
          ·
            refine ⟨131086126460180863689392897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87390750973453909126261931 131086126460180863689392897)
            ·
              refine ⟨98314594845135647767044673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131086126460180863689392897 98314594845135647767044673)
              ·
                refine ⟨73735946133851735825283505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98314594845135647767044673 73735946133851735825283505)
                ·
                  refine ⟨55301959600388801868962629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73735946133851735825283505 55301959600388801868962629)
                  ·
                    refine ⟨10369117425072900350430493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55301959600388801868962629 10369117425072900350430493)
                    ·
                      refine ⟨3888419034402337631411435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369117425072900350430493 3888419034402337631411435)
                      ·
                        rfl

theorem cell23_7572669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_7572669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572669 prefixEnd_7572669 := by exact prefixLift 7572669
  have htrace : WordTrace (prefixWord ++ tailWord_7572669) baseStart_7572669 baseEnd_7572669 := by
    simpa [prefixWord, tailWord_7572669, baseEnd_7572669] using wordTrace_append hprefix tailTrace_7572669
  have hstable : (prefixWord ++ tailWord_7572669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572669).length < 2 ^ (prefixWord ++ tailWord_7572669).sum := by decide
  have hdescent : baseEnd_7572669 < baseStart_7572669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572670 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_7572670 : Nat := 118140960795 + 7572670 * 2 ^ 59
def prefixEnd_7572670 : Nat := 4983230072969 + 3 ^ 40 * 7572670 * 2
def baseEnd_7572670 : Nat := 3888419547882992127498931

theorem tailTrace_7572670 : CollatzResearch.WordTrace tailWord_7572670 prefixEnd_7572670 3888419547882992127498931 := by
  unfold tailWord_7572670
  simp only [CollatzResearch.WordTrace]
  refine ⟨34524745684439671739439433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184131976983678249277010309 34524745684439671739439433)
  ·
    refine ⟨25893559263329753804579575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34524745684439671739439433 25893559263329753804579575)
    ·
      refine ⟨38840338894994630706869363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25893559263329753804579575 38840338894994630706869363)
      ·
        refine ⟨58260508342491946060304045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38840338894994630706869363 58260508342491946060304045)
        ·
          refine ⟨21847690628434479772614017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58260508342491946060304045 21847690628434479772614017)
          ·
            refine ⟨16385767971325859829460513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21847690628434479772614017 16385767971325859829460513)
            ·
              refine ⟨12289325978494394872095385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16385767971325859829460513 12289325978494394872095385)
              ·
                refine ⟨9216994483870796154071539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12289325978494394872095385 9216994483870796154071539)
                ·
                  refine ⟨13825491725806194231107309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9216994483870796154071539 13825491725806194231107309)
                  ·
                    refine ⟨5184559397177322836665241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13825491725806194231107309 5184559397177322836665241)
                    ·
                      refine ⟨3888419547882992127498931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184559397177322836665241 3888419547882992127498931)
                      ·
                        rfl

theorem cell23_7572670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_7572670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572670 prefixEnd_7572670 := by exact prefixLift 7572670
  have htrace : WordTrace (prefixWord ++ tailWord_7572670) baseStart_7572670 baseEnd_7572670 := by
    simpa [prefixWord, tailWord_7572670, baseEnd_7572670] using wordTrace_append hprefix tailTrace_7572670
  have hstable : (prefixWord ++ tailWord_7572670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572670).length < 2 ^ (prefixWord ++ tailWord_7572670).sum := by decide
  have hdescent : baseEnd_7572670 < baseStart_7572670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572678 : List Nat := [6, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7572678 : Nat := 118140960795 + 7572678 * 2 ^ 59
def prefixEnd_7572678 : Nat := 4983230072969 + 3 ^ 40 * 7572678 * 2
def baseEnd_7572678 : Nat := 3888423655728228096198895

theorem tailTrace_7572678 : CollatzResearch.WordTrace tailWord_7572678 prefixEnd_7572678 3888423655728228096198895 := by
  unfold tailWord_7572678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631195539359012227556459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184132171506325594187871125 8631195539359012227556459)
  ·
    refine ⟨12946793309038518341334689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8631195539359012227556459 12946793309038518341334689)
    ·
      refine ⟨9710094981778888756001017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12946793309038518341334689 9710094981778888756001017)
      ·
        refine ⟨7282571236334166567000763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9710094981778888756001017 7282571236334166567000763)
        ·
          refine ⟨10923856854501249850501145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282571236334166567000763 10923856854501249850501145)
          ·
            refine ⟨8192892640875937387875859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10923856854501249850501145 8192892640875937387875859)
            ·
              refine ⟨12289338961313906081813789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8192892640875937387875859 12289338961313906081813789)
              ·
                refine ⟨4608502110492714780680171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12289338961313906081813789 4608502110492714780680171)
                ·
                  refine ⟨6912753165739072171020257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608502110492714780680171 6912753165739072171020257)
                  ·
                    refine ⟨5184564874304304128265193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6912753165739072171020257 5184564874304304128265193)
                    ·
                      refine ⟨3888423655728228096198895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184564874304304128265193 3888423655728228096198895)
                      ·
                        rfl

theorem cell23_7572678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7572678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572678 prefixEnd_7572678 := by exact prefixLift 7572678
  have htrace : WordTrace (prefixWord ++ tailWord_7572678) baseStart_7572678 baseEnd_7572678 := by
    simpa [prefixWord, tailWord_7572678, baseEnd_7572678] using wordTrace_append hprefix tailTrace_7572678
  have hstable : (prefixWord ++ tailWord_7572678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572678).length < 2 ^ (prefixWord ++ tailWord_7572678).sum := by decide
  have hdescent : baseEnd_7572678 < baseStart_7572678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572686 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_7572686 : Nat := 118140960795 + 7572686 * 2 ^ 59
def prefixEnd_7572686 : Nat := 4983230072969 + 3 ^ 40 * 7572686 * 2
def baseEnd_7572686 : Nat := 3888427763573464064898857

theorem tailTrace_7572686 : CollatzResearch.WordTrace tailWord_7572686 prefixEnd_7572686 3888427763573464064898857 := by
  unfold tailWord_7572686
  simp only [CollatzResearch.WordTrace]
  refine ⟨34524818630432426081012239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184132366028972939098731941 34524818630432426081012239)
  ·
    refine ⟨51787227945648639121518359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34524818630432426081012239 51787227945648639121518359)
    ·
      refine ⟨77680841918472958682277539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51787227945648639121518359 77680841918472958682277539)
      ·
        refine ⟨116521262877709438023416309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77680841918472958682277539 116521262877709438023416309)
        ·
          refine ⟨10923868394785259814695279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116521262877709438023416309 10923868394785259814695279)
          ·
            refine ⟨16385802592177889722042919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923868394785259814695279 16385802592177889722042919)
            ·
              refine ⟨24578703888266834583064379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16385802592177889722042919 24578703888266834583064379)
              ·
                refine ⟨36868055832400251874596569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24578703888266834583064379 36868055832400251874596569)
                ·
                  refine ⟨27651041874300188905947427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36868055832400251874596569 27651041874300188905947427)
                  ·
                    refine ⟨41476562811450283358921141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27651041874300188905947427 41476562811450283358921141)
                    ·
                      refine ⟨3888427763573464064898857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41476562811450283358921141 3888427763573464064898857)
                      ·
                        rfl

theorem cell23_7572686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_7572686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572686 prefixEnd_7572686 := by exact prefixLift 7572686
  have htrace : WordTrace (prefixWord ++ tailWord_7572686) baseStart_7572686 baseEnd_7572686 := by
    simpa [prefixWord, tailWord_7572686, baseEnd_7572686] using wordTrace_append hprefix tailTrace_7572686
  have hstable : (prefixWord ++ tailWord_7572686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572686).length < 2 ^ (prefixWord ++ tailWord_7572686).sum := by decide
  have hdescent : baseEnd_7572686 < baseStart_7572686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572717 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_7572717 : Nat := 118140960795 + 7572717 * 2 ^ 59
def prefixEnd_7572717 : Nat := 4983230072969 + 3 ^ 40 * 7572717 * 2
def baseEnd_7572717 : Nat := 3888443681473753443611215

theorem tailTrace_7572717 : CollatzResearch.WordTrace tailWord_7572717 prefixEnd_7572717 3888443681473753443611215 := by
  unfold tailWord_7572717
  simp only [CollatzResearch.WordTrace]
  refine ⟨276199679706347100942476405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184133119804231400628317603 276199679706347100942476405)
  ·
    refine ⟨25893719972470040713357163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276199679706347100942476405 25893719972470040713357163)
    ·
      refine ⟨38840579958705061070035745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25893719972470040713357163 38840579958705061070035745)
      ·
        refine ⟨29130434969028795802526809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38840579958705061070035745 29130434969028795802526809)
        ·
          refine ⟨21847826226771596851895107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29130434969028795802526809 21847826226771596851895107)
          ·
            refine ⟨32771739340157395277842661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21847826226771596851895107 32771739340157395277842661)
            ·
              refine ⟨6144701126279511614595499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32771739340157395277842661 6144701126279511614595499)
              ·
                refine ⟨9217051689419267421893249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144701126279511614595499 9217051689419267421893249)
                ·
                  refine ⟨6912788767064450566419937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9217051689419267421893249 6912788767064450566419937)
                  ·
                    refine ⟨5184591575298337924814953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6912788767064450566419937 5184591575298337924814953)
                    ·
                      refine ⟨3888443681473753443611215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184591575298337924814953 3888443681473753443611215)
                      ·
                        rfl

theorem cell23_7572717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_7572717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572717 prefixEnd_7572717 := by exact prefixLift 7572717
  have htrace : WordTrace (prefixWord ++ tailWord_7572717) baseStart_7572717 baseEnd_7572717 := by
    simpa [prefixWord, tailWord_7572717, baseEnd_7572717] using wordTrace_append hprefix tailTrace_7572717
  have hstable : (prefixWord ++ tailWord_7572717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572717).length < 2 ^ (prefixWord ++ tailWord_7572717).sum := by decide
  have hdescent : baseEnd_7572717 < baseStart_7572717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572759 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_7572759 : Nat := 118140960795 + 7572759 * 2 ^ 59
def prefixEnd_7572759 : Nat := 4983230072969 + 3 ^ 40 * 7572759 * 2
def baseEnd_7572759 : Nat := 3888465247661242279286021

theorem tailTrace_7572759 : CollatzResearch.WordTrace tailWord_7572759 prefixEnd_7572759 3888465247661242279286021 := by
  unfold tailWord_7572759
  simp only [CollatzResearch.WordTrace]
  refine ⟨276201211572194942115505331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184134141048129961410336887 276201211572194942115505331)
  ·
    refine ⟨414301817358292413173257997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276201211572194942115505331 414301817358292413173257997)
    ·
      refine ⟨155363181509359654939971749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414301817358292413173257997 155363181509359654939971749)
      ·
        refine ⟨29130596533004935301244703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155363181509359654939971749 29130596533004935301244703)
        ·
          refine ⟨43695894799507402951867055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29130596533004935301244703 43695894799507402951867055)
          ·
            refine ⟨65543842199261104427800583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43695894799507402951867055 65543842199261104427800583)
            ·
              refine ⟨98315763298891656641700875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65543842199261104427800583 98315763298891656641700875)
              ·
                refine ⟨147473644948337484962551313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98315763298891656641700875 147473644948337484962551313)
                ·
                  refine ⟨110605233711253113721913485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147473644948337484962551313 110605233711253113721913485)
                  ·
                    refine ⟨41476962641719917645717557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110605233711253113721913485 41476962641719917645717557)
                    ·
                      refine ⟨3888465247661242279286021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41476962641719917645717557 3888465247661242279286021)
                      ·
                        rfl

theorem cell23_7572759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_7572759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572759 prefixEnd_7572759 := by exact prefixLift 7572759
  have htrace : WordTrace (prefixWord ++ tailWord_7572759) baseStart_7572759 baseEnd_7572759 := by
    simpa [prefixWord, tailWord_7572759, baseEnd_7572759] using wordTrace_append hprefix tailTrace_7572759
  have hstable : (prefixWord ++ tailWord_7572759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572759).length < 2 ^ (prefixWord ++ tailWord_7572759).sum := by decide
  have hdescent : baseEnd_7572759 < baseStart_7572759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572769 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7572769 : Nat := 118140960795 + 7572769 * 2 ^ 59
def prefixEnd_7572769 : Nat := 4983230072969 + 3 ^ 40 * 7572769 * 2
def baseEnd_7572769 : Nat := 3888470382467787240160975

theorem tailTrace_7572769 : CollatzResearch.WordTrace tailWord_7572769 prefixEnd_7572769 3888470382467787240160975 := by
  unfold tailWord_7572769
  simp only [CollatzResearch.WordTrace]
  refine ⟨276201576302158713823369361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184134384201439142548912907 276201576302158713823369361)
  ·
    refine ⟨207151182226619035367527021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276201576302158713823369361 207151182226619035367527021)
    ·
      refine ⟨77681693334982138262822633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207151182226619035367527021 77681693334982138262822633)
      ·
        refine ⟨58261270001236603697116975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77681693334982138262822633 58261270001236603697116975)
        ·
          refine ⟨87391905001854905545675463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58261270001236603697116975 87391905001854905545675463)
          ·
            refine ⟨131087857502782358318513195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87391905001854905545675463 131087857502782358318513195)
            ·
              refine ⟨196631786254173537477769793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131087857502782358318513195 196631786254173537477769793)
              ·
                refine ⟨147473839690630153108327345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196631786254173537477769793 147473839690630153108327345)
                ·
                  refine ⟨110605379767972614831245509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147473839690630153108327345 110605379767972614831245509)
                  ·
                    refine ⟨20738508706494865280858533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110605379767972614831245509 20738508706494865280858533)
                    ·
                      refine ⟨3888470382467787240160975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20738508706494865280858533 3888470382467787240160975)
                      ·
                        rfl

theorem cell23_7572769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7572769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572769 prefixEnd_7572769 := by exact prefixLift 7572769
  have htrace : WordTrace (prefixWord ++ tailWord_7572769) baseStart_7572769 baseEnd_7572769 := by
    simpa [prefixWord, tailWord_7572769, baseEnd_7572769] using wordTrace_append hprefix tailTrace_7572769
  have hstable : (prefixWord ++ tailWord_7572769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572769).length < 2 ^ (prefixWord ++ tailWord_7572769).sum := by decide
  have hdescent : baseEnd_7572769 < baseStart_7572769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572773 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 2, 4, 2]
def baseStart_7572773 : Nat := 118140960795 + 7572773 * 2 ^ 59
def prefixEnd_7572773 : Nat := 4983230072969 + 3 ^ 40 * 7572773 * 2
def baseEnd_7572773 : Nat := 3888472436390405224510957

theorem tailTrace_7572773 : CollatzResearch.WordTrace tailWord_7572773 prefixEnd_7572773 3888472436390405224510957 := by
  unfold tailWord_7572773
  simp only [CollatzResearch.WordTrace]
  refine ⟨276201722194144222506514973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184134481462762815004343315 276201722194144222506514973)
  ·
    refine ⟨103575645822804083439943115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276201722194144222506514973 103575645822804083439943115)
    ·
      refine ⟨155363468734206125159914673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103575645822804083439943115 155363468734206125159914673)
      ·
        refine ⟨116522601550654593869936005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155363468734206125159914673 116522601550654593869936005)
        ·
          refine ⟨21847987790747736350613001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116522601550654593869936005 21847987790747736350613001)
          ·
            refine ⟨16385990843060802262959751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21847987790747736350613001 16385990843060802262959751)
            ·
              refine ⟨24578986264591203394439627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16385990843060802262959751 24578986264591203394439627)
              ·
                refine ⟨36868479396886805091659441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24578986264591203394439627 36868479396886805091659441)
                ·
                  refine ⟨27651359547665103818744581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36868479396886805091659441 27651359547665103818744581)
                  ·
                    refine ⟨5184629915187206966014609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27651359547665103818744581 5184629915187206966014609)
                    ·
                      refine ⟨3888472436390405224510957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184629915187206966014609 3888472436390405224510957)
                      ·
                        rfl

theorem cell23_7572773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_7572773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572773 prefixEnd_7572773 := by exact prefixLift 7572773
  have htrace : WordTrace (prefixWord ++ tailWord_7572773) baseStart_7572773 baseEnd_7572773 := by
    simpa [prefixWord, tailWord_7572773, baseEnd_7572773] using wordTrace_append hprefix tailTrace_7572773
  have hstable : (prefixWord ++ tailWord_7572773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572773).length < 2 ^ (prefixWord ++ tailWord_7572773).sum := by decide
  have hdescent : baseEnd_7572773 < baseStart_7572773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572790 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7572790 : Nat := 118140960795 + 7572790 * 2 ^ 59
def prefixEnd_7572790 : Nat := 4983230072969 + 3 ^ 40 * 7572790 * 2
def baseEnd_7572790 : Nat := 3888481165561531657998379

theorem tailTrace_7572790 : CollatzResearch.WordTrace tailWord_7572790 prefixEnd_7572790 3888481165561531657998379 := by
  unfold tailWord_7572790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17262646389692664650617739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184134894823388422939922549 17262646389692664650617739)
  ·
    refine ⟨25893969584538996975926609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17262646389692664650617739 25893969584538996975926609)
    ·
      refine ⟨19420477188404247731944957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25893969584538996975926609 19420477188404247731944957)
      ·
        refine ⟨7282678945651592899479359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19420477188404247731944957 7282678945651592899479359)
        ·
          refine ⟨10924018418477389349219039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7282678945651592899479359 10924018418477389349219039)
          ·
            refine ⟨16386027627716084023828559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10924018418477389349219039 16386027627716084023828559)
            ·
              refine ⟨24579041441574126035742839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16386027627716084023828559 24579041441574126035742839)
              ·
                refine ⟨36868562162361189053614259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24579041441574126035742839 36868562162361189053614259)
                ·
                  refine ⟨55302843243541783580421389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36868562162361189053614259 55302843243541783580421389)
                  ·
                    refine ⟨20738566216328168842658021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55302843243541783580421389 20738566216328168842658021)
                    ·
                      refine ⟨3888481165561531657998379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20738566216328168842658021 3888481165561531657998379)
                      ·
                        rfl

theorem cell23_7572790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7572790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572790 prefixEnd_7572790 := by exact prefixLift 7572790
  have htrace : WordTrace (prefixWord ++ tailWord_7572790) baseStart_7572790 baseEnd_7572790 := by
    simpa [prefixWord, tailWord_7572790, baseEnd_7572790] using wordTrace_append hprefix tailTrace_7572790
  have hstable : (prefixWord ++ tailWord_7572790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572790).length < 2 ^ (prefixWord ++ tailWord_7572790).sum := by decide
  have hdescent : baseEnd_7572790 < baseStart_7572790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572793 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7572793 : Nat := 118140960795 + 7572793 * 2 ^ 59
def prefixEnd_7572793 : Nat := 4983230072969 + 3 ^ 40 * 7572793 * 2
def baseEnd_7572793 : Nat := 3888482706003495146260865

theorem tailTrace_7572793 : CollatzResearch.WordTrace tailWord_7572793 prefixEnd_7572793 3888482706003495146260865 := by
  unfold tailWord_7572793
  simp only [CollatzResearch.WordTrace]
  refine ⟨276202451654071765922243033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184134967769381177281495355 276202451654071765922243033)
  ·
    refine ⟨207151838740553824441682275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276202451654071765922243033 207151838740553824441682275)
    ·
      refine ⟨310727758110830736662523413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207151838740553824441682275 310727758110830736662523413)
      ·
        refine ⟨14565363661445190781055785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 310727758110830736662523413 14565363661445190781055785)
        ·
          refine ⟨10924022746083893085791839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14565363661445190781055785 10924022746083893085791839)
          ·
            refine ⟨16386034119125839628687759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10924022746083893085791839 16386034119125839628687759)
            ·
              refine ⟨24579051178688759443031639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16386034119125839628687759 24579051178688759443031639)
              ·
                refine ⟨36868576768033139164547459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24579051178688759443031639 36868576768033139164547459)
                ·
                  refine ⟨55302865152049708746821189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36868576768033139164547459 55302865152049708746821189)
                  ·
                    refine ⟨10369287216009320390028973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55302865152049708746821189 10369287216009320390028973)
                    ·
                      refine ⟨3888482706003495146260865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369287216009320390028973 3888482706003495146260865)
                      ·
                        rfl

theorem cell23_7572793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7572793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572793 prefixEnd_7572793 := by exact prefixLift 7572793
  have htrace : WordTrace (prefixWord ++ tailWord_7572793) baseStart_7572793 baseEnd_7572793 := by
    simpa [prefixWord, tailWord_7572793, baseEnd_7572793] using wordTrace_append hprefix tailTrace_7572793
  have hstable : (prefixWord ++ tailWord_7572793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572793).length < 2 ^ (prefixWord ++ tailWord_7572793).sum := by decide
  have hdescent : baseEnd_7572793 < baseStart_7572793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572823 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_7572823 : Nat := 118140960795 + 7572823 * 2 ^ 59
def prefixEnd_7572823 : Nat := 4983230072969 + 3 ^ 40 * 7572823 * 2
def baseEnd_7572823 : Nat := 3888498110423130028885727

theorem tailTrace_7572823 : CollatzResearch.WordTrace tailWord_7572823 prefixEnd_7572823 3888498110423130028885727 := by
  unfold tailWord_7572823
  simp only [CollatzResearch.WordTrace]
  refine ⟨276203545843963081045835123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184135697229308720697223415 276203545843963081045835123)
  ·
    refine ⟨414305318765944621568752685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276203545843963081045835123 414305318765944621568752685)
    ·
      refine ⟨155364494537229233088282257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414305318765944621568752685 155364494537229233088282257)
      ·
        refine ⟨116523370902921924816211693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155364494537229233088282257 116523370902921924816211693)
        ·
          refine ⟨43696264088595721806079385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116523370902921924816211693 43696264088595721806079385)
          ·
            refine ⟨32772198066446791354559539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43696264088595721806079385 32772198066446791354559539)
            ·
              refine ⟨49158297099670187031839309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32772198066446791354559539 49158297099670187031839309)
              ·
                refine ⟨18434361412376320136939741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49158297099670187031839309 18434361412376320136939741)
                ·
                  refine ⟨6912885529641120051352403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18434361412376320136939741 6912885529641120051352403)
                  ·
                    refine ⟨10369328294461680077028605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6912885529641120051352403 10369328294461680077028605)
                    ·
                      refine ⟨3888498110423130028885727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369328294461680077028605 3888498110423130028885727)
                      ·
                        rfl

theorem cell23_7572823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_7572823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572823 prefixEnd_7572823 := by exact prefixLift 7572823
  have htrace : WordTrace (prefixWord ++ tailWord_7572823) baseStart_7572823 baseEnd_7572823 := by
    simpa [prefixWord, tailWord_7572823, baseEnd_7572823] using wordTrace_append hprefix tailTrace_7572823
  have hstable : (prefixWord ++ tailWord_7572823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572823).length < 2 ^ (prefixWord ++ tailWord_7572823).sum := by decide
  have hdescent : baseEnd_7572823 < baseStart_7572823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572869 : List Nat := [1, 3, 1, 1, 3, 1, 13]
def baseStart_7572869 : Nat := 118140960795 + 7572869 * 2 ^ 59
def prefixEnd_7572869 : Nat := 4983230072969 + 3 ^ 40 * 7572869 * 2
def baseEnd_7572869 : Nat := 48006441117694282085315

theorem tailTrace_7572869 : CollatzResearch.WordTrace tailWord_7572869 prefixEnd_7572869 48006441117694282085315 := by
  unfold tailWord_7572869
  simp only [CollatzResearch.WordTrace]
  refine ⟨276205223601796430902009661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184136815734530953934673107 276205223601796430902009661)
  ·
    refine ⟨103576958850673661588253623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276205223601796430902009661 103576958850673661588253623)
    ·
      refine ⟨155365438276010492382380435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103576958850673661588253623 155365438276010492382380435)
      ·
        refine ⟨233048157414015738573570653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155365438276010492382380435 233048157414015738573570653)
        ·
          refine ⟨87393059030255901965088995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233048157414015738573570653 87393059030255901965088995)
          ·
            refine ⟨131089588545383852947633493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87393059030255901965088995 131089588545383852947633493)
            ·
              refine ⟨48006441117694282085315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 131089588545383852947633493 48006441117694282085315)
              ·
                rfl

theorem cell23_7572869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 13].length) (baseStart_7572869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572869 prefixEnd_7572869 := by exact prefixLift 7572869
  have htrace : WordTrace (prefixWord ++ tailWord_7572869) baseStart_7572869 baseEnd_7572869 := by
    simpa [prefixWord, tailWord_7572869, baseEnd_7572869] using wordTrace_append hprefix tailTrace_7572869
  have hstable : (prefixWord ++ tailWord_7572869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572869).length < 2 ^ (prefixWord ++ tailWord_7572869).sum := by decide
  have hdescent : baseEnd_7572869 < baseStart_7572869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572894 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_7572894 : Nat := 118140960795 + 7572894 * 2 ^ 59
def prefixEnd_7572894 : Nat := 4983230072969 + 3 ^ 40 * 7572894 * 2
def baseEnd_7572894 : Nat := 1296178189183199750365967

theorem tailTrace_7572894 : CollatzResearch.WordTrace tailWord_7572894 prefixEnd_7572894 1296178189183199750365967 := by
  unfold tailWord_7572894
  simp only [CollatzResearch.WordTrace]
  refine ⟨34525766928338232521458717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184137423617803906781113157 34525766928338232521458717)
  ·
    refine ⟨12947162598126837195547019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34525766928338232521458717 12947162598126837195547019)
    ·
      refine ⟨19420743897190255793320529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12947162598126837195547019 19420743897190255793320529)
      ·
        refine ⟨14565557922892691844990397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19420743897190255793320529 14565557922892691844990397)
        ·
          refine ⟨5462084221084759441871399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14565557922892691844990397 5462084221084759441871399)
          ·
            refine ⟨8193126331627139162807099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462084221084759441871399 8193126331627139162807099)
            ·
              refine ⟨12289689497440708744210649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8193126331627139162807099 12289689497440708744210649)
              ·
                refine ⟨9217267123080531558157987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12289689497440708744210649 9217267123080531558157987)
                ·
                  refine ⟨13825900684620797337236981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9217267123080531558157987 13825900684620797337236981)
                  ·
                    refine ⟨1296178189183199750365967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13825900684620797337236981 1296178189183199750365967)
                    ·
                      rfl

theorem cell23_7572894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_7572894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572894 prefixEnd_7572894 := by exact prefixLift 7572894
  have htrace : WordTrace (prefixWord ++ tailWord_7572894) baseStart_7572894 baseEnd_7572894 := by
    simpa [prefixWord, tailWord_7572894, baseEnd_7572894] using wordTrace_append hprefix tailTrace_7572894
  have hstable : (prefixWord ++ tailWord_7572894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572894).length < 2 ^ (prefixWord ++ tailWord_7572894).sum := by decide
  have hdescent : baseEnd_7572894 < baseStart_7572894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572913 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_7572913 : Nat := 118140960795 + 7572913 * 2 ^ 59
def prefixEnd_7572913 : Nat := 4983230072969 + 3 ^ 40 * 7572913 * 2
def baseEnd_7572913 : Nat := 3888544323682034676760313

theorem tailTrace_7572913 : CollatzResearch.WordTrace tailWord_7572913 prefixEnd_7572913 3888544323682034676760313 := by
  unfold tailWord_7572913
  simp only [CollatzResearch.WordTrace]
  refine ⟨276206828413637026416611393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184137885609091350944407595 276206828413637026416611393)
  ·
    refine ⟨207155121310227769812458545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276206828413637026416611393 207155121310227769812458545)
    ·
      refine ⟨155366340982670827359343909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207155121310227769812458545 155366340982670827359343909)
      ·
        refine ⟨29131188934250780129876983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155366340982670827359343909 29131188934250780129876983)
        ·
          refine ⟨43696783401376170194815475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29131188934250780129876983 43696783401376170194815475)
          ·
            refine ⟨65545175102064255292223213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43696783401376170194815475 65545175102064255292223213)
            ·
              refine ⟨24579440663274095734583705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65545175102064255292223213 24579440663274095734583705)
              ·
                refine ⟨18434580497455571800937779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24579440663274095734583705 18434580497455571800937779)
                ·
                  refine ⟨27651870746183357701406669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18434580497455571800937779 27651870746183357701406669)
                  ·
                    refine ⟨10369451529818759138027501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27651870746183357701406669 10369451529818759138027501)
                    ·
                      refine ⟨3888544323682034676760313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369451529818759138027501 3888544323682034676760313)
                      ·
                        rfl

theorem cell23_7572913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_7572913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572913 prefixEnd_7572913 := by exact prefixLift 7572913
  have htrace : WordTrace (prefixWord ++ tailWord_7572913) baseStart_7572913 baseEnd_7572913 := by
    simpa [prefixWord, tailWord_7572913, baseEnd_7572913] using wordTrace_append hprefix tailTrace_7572913
  have hstable : (prefixWord ++ tailWord_7572913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572913).length < 2 ^ (prefixWord ++ tailWord_7572913).sum := by decide
  have hdescent : baseEnd_7572913 < baseStart_7572913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572917 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_7572917 : Nat := 118140960795 + 7572917 * 2 ^ 59
def prefixEnd_7572917 : Nat := 4983230072969 + 3 ^ 40 * 7572917 * 2
def baseEnd_7572917 : Nat := 3888546377604652661110295

theorem tailTrace_7572917 : CollatzResearch.WordTrace tailWord_7572917 prefixEnd_7572917 3888546377604652661110295 := by
  unfold tailWord_7572917
  simp only [CollatzResearch.WordTrace]
  refine ⟨276206974305622535099757005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184137982870415023399838003 276206974305622535099757005)
  ·
    refine ⟨103577615364608450662408877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276206974305622535099757005 103577615364608450662408877)
    ·
      refine ⟨38841605761728168998403329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103577615364608450662408877 38841605761728168998403329)
      ·
        refine ⟨29131204321296126748802497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38841605761728168998403329 29131204321296126748802497)
        ·
          refine ⟨21848403240972095061601873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29131204321296126748802497 21848403240972095061601873)
          ·
            refine ⟨16386302430729071296201405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21848403240972095061601873 16386302430729071296201405)
            ·
              refine ⟨6144863411523401736075527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16386302430729071296201405 6144863411523401736075527)
              ·
                refine ⟨9217295117285102604113291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144863411523401736075527 9217295117285102604113291)
                ·
                  refine ⟨13825942675927653906169937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9217295117285102604113291 13825942675927653906169937)
                  ·
                    refine ⟨10369457006945740429627453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13825942675927653906169937 10369457006945740429627453)
                    ·
                      refine ⟨3888546377604652661110295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369457006945740429627453 3888546377604652661110295)
                      ·
                        rfl

theorem cell23_7572917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_7572917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572917 prefixEnd_7572917 := by exact prefixLift 7572917
  have htrace : WordTrace (prefixWord ++ tailWord_7572917) baseStart_7572917 baseEnd_7572917 := by
    simpa [prefixWord, tailWord_7572917, baseEnd_7572917] using wordTrace_append hprefix tailTrace_7572917
  have hstable : (prefixWord ++ tailWord_7572917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572917).length < 2 ^ (prefixWord ++ tailWord_7572917).sum := by decide
  have hdescent : baseEnd_7572917 < baseStart_7572917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572936 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_7572936 : Nat := 118140960795 + 7572936 * 2 ^ 59
def prefixEnd_7572936 : Nat := 4983230072969 + 3 ^ 40 * 7572936 * 2
def baseEnd_7572936 : Nat := 3888556133737088086772707

theorem tailTrace_7572936 : CollatzResearch.WordTrace tailWord_7572936 prefixEnd_7572936 3888556133737088086772707 := by
  unfold tailWord_7572936
  simp only [CollatzResearch.WordTrace]
  refine ⟨138103833646276850672349331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184138444861702467563132441 138103833646276850672349331)
  ·
    refine ⟨207155750469415276008523997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138103833646276850672349331 207155750469415276008523997)
    ·
      refine ⟨77683406426030728503196499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207155750469415276008523997 77683406426030728503196499)
      ·
        refine ⟨116525109639046092754794749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77683406426030728503196499 116525109639046092754794749)
        ·
          refine ⟨43696916114642284783048031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116525109639046092754794749 43696916114642284783048031)
          ·
            refine ⟨65545374171963427174572047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43696916114642284783048031 65545374171963427174572047)
            ·
              refine ⟨98318061257945140761858071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65545374171963427174572047 98318061257945140761858071)
              ·
                refine ⟨147477091886917711142787107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98318061257945140761858071 147477091886917711142787107)
                ·
                  refine ⟨221215637830376566714180661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147477091886917711142787107 221215637830376566714180661)
                  ·
                    refine ⟨20738966046597803129454437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 221215637830376566714180661 20738966046597803129454437)
                    ·
                      refine ⟨3888556133737088086772707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20738966046597803129454437 3888556133737088086772707)
                      ·
                        rfl

theorem cell23_7572936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_7572936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572936 prefixEnd_7572936 := by exact prefixLift 7572936
  have htrace : WordTrace (prefixWord ++ tailWord_7572936) baseStart_7572936 baseEnd_7572936 := by
    simpa [prefixWord, tailWord_7572936, baseEnd_7572936] using wordTrace_append hprefix tailTrace_7572936
  have hstable : (prefixWord ++ tailWord_7572936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572936).length < 2 ^ (prefixWord ++ tailWord_7572936).sum := by decide
  have hdescent : baseEnd_7572936 < baseStart_7572936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572940 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 3, 3, 2]
def baseStart_7572940 : Nat := 118140960795 + 7572940 * 2 ^ 59
def prefixEnd_7572940 : Nat := 4983230072969 + 3 ^ 40 * 7572940 * 2
def baseEnd_7572940 : Nat := 3888558187659706071122689

theorem tailTrace_7572940 : CollatzResearch.WordTrace tailWord_7572940 prefixEnd_7572940 3888558187659706071122689 := by
  unfold tailWord_7572940
  simp only [CollatzResearch.WordTrace]
  refine ⟨138103906592269605013922137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184138542123026140018562849 138103906592269605013922137)
  ·
    refine ⟨103577929944202203760441603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138103906592269605013922137 103577929944202203760441603)
    ·
      refine ⟨155366894916303305640662405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103577929944202203760441603 155366894916303305640662405)
      ·
        refine ⟨29131292796806869807624201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155366894916303305640662405 29131292796806869807624201)
        ·
          refine ⟨21848469597605152355718151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29131292796806869807624201 21848469597605152355718151)
          ·
            refine ⟨32772704396407728533577227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21848469597605152355718151 32772704396407728533577227)
            ·
              refine ⟨49159056594611592800365841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32772704396407728533577227 49159056594611592800365841)
              ·
                refine ⟨36869292445958694600274381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49159056594611592800365841 36869292445958694600274381)
                ·
                  refine ⟨13825984667234510475102893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36869292445958694600274381 13825984667234510475102893)
                  ·
                    refine ⟨5184744250212941428163585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13825984667234510475102893 5184744250212941428163585)
                    ·
                      refine ⟨3888558187659706071122689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184744250212941428163585 3888558187659706071122689)
                      ·
                        rfl

theorem cell23_7572940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_7572940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572940 prefixEnd_7572940 := by exact prefixLift 7572940
  have htrace : WordTrace (prefixWord ++ tailWord_7572940) baseStart_7572940 baseEnd_7572940 := by
    simpa [prefixWord, tailWord_7572940, baseEnd_7572940] using wordTrace_append hprefix tailTrace_7572940
  have hstable : (prefixWord ++ tailWord_7572940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572940).length < 2 ^ (prefixWord ++ tailWord_7572940).sum := by decide
  have hdescent : baseEnd_7572940 < baseStart_7572940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7572998 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_7572998 : Nat := 118140960795 + 7572998 * 2 ^ 59
def prefixEnd_7572998 : Nat := 4983230072969 + 3 ^ 40 * 7572998 * 2
def baseEnd_7572998 : Nat := 3888587969537666844197423

theorem tailTrace_7572998 : CollatzResearch.WordTrace tailWord_7572998 prefixEnd_7572998 3888587969537666844197423 := by
  unfold tailWord_7572998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631560269322783935420489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184139952412219390622303765 8631560269322783935420489)
  ·
    refine ⟨6473670201992087951565367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8631560269322783935420489 6473670201992087951565367)
    ·
      refine ⟨9710505302988131927348051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473670201992087951565367 9710505302988131927348051)
      ·
        refine ⟨14565757954482197891022077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9710505302988131927348051 14565757954482197891022077)
        ·
          refine ⟨5462159232930824209133279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14565757954482197891022077 5462159232930824209133279)
          ·
            refine ⟨8193238849396236313699919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462159232930824209133279 8193238849396236313699919)
            ·
              refine ⟨12289858274094354470549879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8193238849396236313699919 12289858274094354470549879)
              ·
                refine ⟨18434787411141531705824819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12289858274094354470549879 18434787411141531705824819)
                ·
                  refine ⟨27652181116712297558737229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18434787411141531705824819 27652181116712297558737229)
                  ·
                    refine ⟨10369567918767111584526461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27652181116712297558737229 10369567918767111584526461)
                    ·
                      refine ⟨3888587969537666844197423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369567918767111584526461 3888587969537666844197423)
                      ·
                        rfl

theorem cell23_7572998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_7572998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7572998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7572998 prefixEnd_7572998 := by exact prefixLift 7572998
  have htrace : WordTrace (prefixWord ++ tailWord_7572998) baseStart_7572998 baseEnd_7572998 := by
    simpa [prefixWord, tailWord_7572998, baseEnd_7572998] using wordTrace_append hprefix tailTrace_7572998
  have hstable : (prefixWord ++ tailWord_7572998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7572998).length < 2 ^ (prefixWord ++ tailWord_7572998).sum := by decide
  have hdescent : baseEnd_7572998 < baseStart_7572998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7572998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573004 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 1, 4, 2]
def baseStart_7573004 : Nat := 118140960795 + 7573004 * 2 ^ 59
def prefixEnd_7573004 : Nat := 4983230072969 + 3 ^ 40 * 7573004 * 2
def baseEnd_7573004 : Nat := 3888591050421593820722395

theorem tailTrace_7573004 : CollatzResearch.WordTrace tailWord_7573004 prefixEnd_7573004 3888591050421593820722395 := by
  unfold tailWord_7573004
  simp only [CollatzResearch.WordTrace]
  refine ⟨138105073728153674479087033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184140098304204899305449377 138105073728153674479087033)
  ·
    refine ⟨103578805296115255859315275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138105073728153674479087033 103578805296115255859315275)
    ·
      refine ⟨155368207944172883788972913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103578805296115255859315275 155368207944172883788972913)
      ·
        refine ⟨116526155958129662841729685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155368207944172883788972913 116526155958129662841729685)
        ·
          refine ⟨5462163560537327945706079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116526155958129662841729685 5462163560537327945706079)
          ·
            refine ⟨8193245340805991918559119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462163560537327945706079 8193245340805991918559119)
            ·
              refine ⟨12289868011208987877838679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8193245340805991918559119 12289868011208987877838679)
              ·
                refine ⟨18434802016813481816758019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12289868011208987877838679 18434802016813481816758019)
                ·
                  refine ⟨27652203025220222725137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18434802016813481816758019 27652203025220222725137029)
                  ·
                    refine ⟨5184788067228791760963193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27652203025220222725137029 5184788067228791760963193)
                    ·
                      refine ⟨3888591050421593820722395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184788067228791760963193 3888591050421593820722395)
                      ·
                        rfl

theorem cell23_7573004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_7573004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573004 prefixEnd_7573004 := by exact prefixLift 7573004
  have htrace : WordTrace (prefixWord ++ tailWord_7573004) baseStart_7573004 baseEnd_7573004 := by
    simpa [prefixWord, tailWord_7573004, baseEnd_7573004] using wordTrace_append hprefix tailTrace_7573004
  have hstable : (prefixWord ++ tailWord_7573004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573004).length < 2 ^ (prefixWord ++ tailWord_7573004).sum := by decide
  have hdescent : baseEnd_7573004 < baseStart_7573004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573027 : List Nat := [1, 1, 1, 4, 5, 2, 1, 3, 5]
def baseStart_7573027 : Nat := 118140960795 + 7573027 * 2 ^ 59
def prefixEnd_7573027 : Nat := 4983230072969 + 3 ^ 40 * 7573027 * 2
def baseEnd_7573027 : Nat := 432066984497405247859421

theorem tailTrace_7573027 : CollatzResearch.WordTrace tailWord_7573027 prefixEnd_7573027 432066984497405247859421 := by
  unfold tailWord_7573027
  simp only [CollatzResearch.WordTrace]
  refine ⟨276210986335224023886261335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184140657556816015924174223 276210986335224023886261335)
  ·
    refine ⟨414316479502836035829392003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276210986335224023886261335 414316479502836035829392003)
    ·
      refine ⟨621474719254254053744088005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414316479502836035829392003 621474719254254053744088005)
      ·
        refine ⟨116526509860172635077016501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 621474719254254053744088005 116526509860172635077016501)
        ·
          refine ⟨10924360299391184538470297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116526509860172635077016501 10924360299391184538470297)
          ·
            refine ⟨8193270224543388403852723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10924360299391184538470297 8193270224543388403852723)
            ·
              refine ⟨12289905336815082605779085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8193270224543388403852723 12289905336815082605779085)
              ·
                refine ⟨4608714501305655977167157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12289905336815082605779085 4608714501305655977167157)
                ·
                  refine ⟨432066984497405247859421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4608714501305655977167157 432066984497405247859421)
                  ·
                    rfl

theorem cell23_7573027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 5].length) (baseStart_7573027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573027 prefixEnd_7573027 := by exact prefixLift 7573027
  have htrace : WordTrace (prefixWord ++ tailWord_7573027) baseStart_7573027 baseEnd_7573027 := by
    simpa [prefixWord, tailWord_7573027, baseEnd_7573027] using wordTrace_append hprefix tailTrace_7573027
  have hstable : (prefixWord ++ tailWord_7573027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573027).length < 2 ^ (prefixWord ++ tailWord_7573027).sum := by decide
  have hdescent : baseEnd_7573027 < baseStart_7573027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573043 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 4]
def baseStart_7573043 : Nat := 118140960795 + 7573043 * 2 ^ 59
def prefixEnd_7573043 : Nat := 4983230072969 + 3 ^ 40 * 7573043 * 2
def baseEnd_7573043 : Nat := 3888611076167119168134715

theorem tailTrace_7573043 : CollatzResearch.WordTrace tailWord_7573043 prefixEnd_7573043 3888611076167119168134715 := by
  unfold tailWord_7573043
  simp only [CollatzResearch.WordTrace]
  refine ⟨276211569903166058618843783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184141046602110705745895855 276211569903166058618843783)
  ·
    refine ⟨414317354854749087928265675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276211569903166058618843783 414317354854749087928265675)
    ·
      refine ⟨621476032282123631892398513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414317354854749087928265675 621476032282123631892398513)
      ·
        refine ⟨466107024211592723919298885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621476032282123631892398513 466107024211592723919298885)
        ·
          refine ⟨87395067039673635734868541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466107024211592723919298885 87395067039673635734868541)
          ·
            refine ⟨32773150139877613400575703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87395067039673635734868541 32773150139877613400575703)
            ·
              refine ⟨49159725209816420100863555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32773150139877613400575703 49159725209816420100863555)
              ·
                refine ⟨73739587814724630151295333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49159725209816420100863555 73739587814724630151295333)
                ·
                  refine ⟨13826172715260868153367875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73739587814724630151295333 13826172715260868153367875)
                  ·
                    refine ⟨20739259072891302230051813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13826172715260868153367875 20739259072891302230051813)
                    ·
                      refine ⟨3888611076167119168134715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20739259072891302230051813 3888611076167119168134715)
                      ·
                        rfl

theorem cell23_7573043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_7573043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573043 prefixEnd_7573043 := by exact prefixLift 7573043
  have htrace : WordTrace (prefixWord ++ tailWord_7573043) baseStart_7573043 baseEnd_7573043 := by
    simpa [prefixWord, tailWord_7573043, baseEnd_7573043] using wordTrace_append hprefix tailTrace_7573043
  have hstable : (prefixWord ++ tailWord_7573043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573043).length < 2 ^ (prefixWord ++ tailWord_7573043).sum := by decide
  have hdescent : baseEnd_7573043 < baseStart_7573043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573104 : List Nat := [2, 1, 1, 1, 6, 1, 4, 2, 1, 4]
def baseStart_7573104 : Nat := 118140960795 + 7573104 * 2 ^ 59
def prefixEnd_7573104 : Nat := 4983230072969 + 3 ^ 40 * 7573104 * 2
def baseEnd_7573104 : Nat := 1296214132829014476490645

theorem tailTrace_7573104 : CollatzResearch.WordTrace tailWord_7573104 prefixEnd_7573104 1296214132829014476490645 := by
  unfold tailWord_7573104
  simp only [CollatzResearch.WordTrace]
  refine ⟨138106897377972533018407183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184142529837296710691209577 138106897377972533018407183)
  ·
    refine ⟨207160346066958799527610775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138106897377972533018407183 207160346066958799527610775)
    ·
      refine ⟨310740519100438199291416163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207160346066958799527610775 310740519100438199291416163)
      ·
        refine ⟨466110778650657298937124245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310740519100438199291416163 466110778650657298937124245)
        ·
          refine ⟨21848942749249560887677699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 466110778650657298937124245 21848942749249560887677699)
          ·
            refine ⟨32773414123874341331516549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21848942749249560887677699 32773414123874341331516549)
            ·
              refine ⟨6145015148226438999659353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32773414123874341331516549 6145015148226438999659353)
              ·
                refine ⟨4608761361169829249744515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145015148226438999659353 4608761361169829249744515)
                ·
                  refine ⟨6913142041754743874616773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608761361169829249744515 6913142041754743874616773)
                  ·
                    refine ⟨1296214132829014476490645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6913142041754743874616773 1296214132829014476490645)
                    ·
                      rfl

theorem cell23_7573104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 1, 4].length) (baseStart_7573104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573104 prefixEnd_7573104 := by exact prefixLift 7573104
  have htrace : WordTrace (prefixWord ++ tailWord_7573104) baseStart_7573104 baseEnd_7573104 := by
    simpa [prefixWord, tailWord_7573104, baseEnd_7573104] using wordTrace_append hprefix tailTrace_7573104
  have hstable : (prefixWord ++ tailWord_7573104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573104).length < 2 ^ (prefixWord ++ tailWord_7573104).sum := by decide
  have hdescent : baseEnd_7573104 < baseStart_7573104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573113 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 5, 5]
def baseStart_7573113 : Nat := 118140960795 + 7573113 * 2 ^ 59
def prefixEnd_7573113 : Nat := 4983230072969 + 3 ^ 40 * 7573113 * 2
def baseEnd_7573113 : Nat := 1296215673270977964753131

theorem tailTrace_7573113 : CollatzResearch.WordTrace tailWord_7573113 prefixEnd_7573113 1296215673270977964753131 := by
  unfold tailWord_7573113
  simp only [CollatzResearch.WordTrace]
  refine ⟨276214123012912460573891993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184142748675274973715927995 276214123012912460573891993)
  ·
    refine ⟨207160592259684345430418995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276214123012912460573891993 207160592259684345430418995)
    ·
      refine ⟨310740888389526518145628493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207160592259684345430418995 310740888389526518145628493)
      ·
        refine ⟨116527833146072444304610685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310740888389526518145628493 116527833146072444304610685)
        ·
          refine ⟨43697937429777166614229007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116527833146072444304610685 43697937429777166614229007)
          ·
            refine ⟨65546906144665749921343511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43697937429777166614229007 65546906144665749921343511)
            ·
              refine ⟨98320359216998624882015267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65546906144665749921343511 98320359216998624882015267)
              ·
                refine ⟨147480538825497937323022901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98320359216998624882015267 147480538825497937323022901)
                ·
                  refine ⟨13826300514890431624033397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147480538825497937323022901 13826300514890431624033397)
                  ·
                    refine ⟨1296215673270977964753131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13826300514890431624033397 1296215673270977964753131)
                    ·
                      rfl

theorem cell23_7573113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_7573113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573113 prefixEnd_7573113 := by exact prefixLift 7573113
  have htrace : WordTrace (prefixWord ++ tailWord_7573113) baseStart_7573113 baseEnd_7573113 := by
    simpa [prefixWord, tailWord_7573113, baseEnd_7573113] using wordTrace_append hprefix tailTrace_7573113
  have hstable : (prefixWord ++ tailWord_7573113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573113).length < 2 ^ (prefixWord ++ tailWord_7573113).sum := by decide
  have hdescent : baseEnd_7573113 < baseStart_7573113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573120 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 1, 5, 2]
def baseStart_7573120 : Nat := 118140960795 + 7573120 * 2 ^ 59
def prefixEnd_7573120 : Nat := 4983230072969 + 3 ^ 40 * 7573120 * 2
def baseEnd_7573120 : Nat := 3888650614177515366871861

theorem tailTrace_7573120 : CollatzResearch.WordTrace tailWord_7573120 prefixEnd_7573120 3888650614177515366871861 := by
  unfold tailWord_7573120
  simp only [CollatzResearch.WordTrace]
  refine ⟨138107189161943550384698407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184142918882591400512931209 138107189161943550384698407)
  ·
    refine ⟨207160783742915325577047611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138107189161943550384698407 207160783742915325577047611)
    ·
      refine ⟨310741175614372988365571417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207160783742915325577047611 310741175614372988365571417)
      ·
        refine ⟨233055881710779741274178563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310741175614372988365571417 233055881710779741274178563)
        ·
          refine ⟨349583822566169611911267845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233055881710779741274178563 349583822566169611911267845)
          ·
            refine ⟨65546966731156802233362721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 349583822566169611911267845 65546966731156802233362721)
            ·
              refine ⟨49160225048367601675022041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65546966731156802233362721 49160225048367601675022041)
              ·
                refine ⟨36870168786275701256266531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49160225048367601675022041 36870168786275701256266531)
                ·
                  refine ⟨55305253179413551884399797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36870168786275701256266531 55305253179413551884399797)
                  ·
                    refine ⟨5184867485570020489162481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55305253179413551884399797 5184867485570020489162481)
                    ·
                      refine ⟨3888650614177515366871861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184867485570020489162481 3888650614177515366871861)
                      ·
                        rfl

theorem cell23_7573120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_7573120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573120 prefixEnd_7573120 := by exact prefixLift 7573120
  have htrace : WordTrace (prefixWord ++ tailWord_7573120) baseStart_7573120 baseEnd_7573120 := by
    simpa [prefixWord, tailWord_7573120, baseEnd_7573120] using wordTrace_append hprefix tailTrace_7573120
  have hstable : (prefixWord ++ tailWord_7573120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573120).length < 2 ^ (prefixWord ++ tailWord_7573120).sum := by decide
  have hdescent : baseEnd_7573120 < baseStart_7573120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573127 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_7573127 : Nat := 118140960795 + 7573127 * 2 ^ 59
def prefixEnd_7573127 : Nat := 4983230072969 + 3 ^ 40 * 7573127 * 2
def baseEnd_7573127 : Nat := 3888654208542096839484329

theorem tailTrace_7573127 : CollatzResearch.WordTrace tailWord_7573127 prefixEnd_7573127 3888654208542096839484329 := by
  unfold tailWord_7573127
  simp only [CollatzResearch.WordTrace]
  refine ⟨276214633634861740964901635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184143089089907827309934423 276214633634861740964901635)
  ·
    refine ⟨414321950452292611447352453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276214633634861740964901635 414321950452292611447352453)
    ·
      refine ⟨77685365709804864646378585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414321950452292611447352453 77685365709804864646378585)
      ·
        refine ⟨58264024282353648484783939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77685365709804864646378585 58264024282353648484783939)
        ·
          refine ⟨87396036423530472727175909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58264024282353648484783939 87396036423530472727175909)
          ·
            refine ⟨16386756829411963636345483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87396036423530472727175909 16386756829411963636345483)
            ·
              refine ⟨24580135244117945454518225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16386756829411963636345483 24580135244117945454518225)
              ·
                refine ⟨18435101433088459090888669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24580135244117945454518225 18435101433088459090888669)
                ·
                  refine ⟨6913163037408172159083251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18435101433088459090888669 6913163037408172159083251)
                  ·
                    refine ⟨10369744556112258238624877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6913163037408172159083251 10369744556112258238624877)
                    ·
                      refine ⟨3888654208542096839484329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369744556112258238624877 3888654208542096839484329)
                      ·
                        rfl

theorem cell23_7573127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_7573127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573127 prefixEnd_7573127 := by exact prefixLift 7573127
  have htrace : WordTrace (prefixWord ++ tailWord_7573127) baseStart_7573127 baseEnd_7573127 := by
    simpa [prefixWord, tailWord_7573127, baseEnd_7573127] using wordTrace_append hprefix tailTrace_7573127
  have hstable : (prefixWord ++ tailWord_7573127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573127).length < 2 ^ (prefixWord ++ tailWord_7573127).sum := by decide
  have hdescent : baseEnd_7573127 < baseStart_7573127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573130 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_7573130 : Nat := 118140960795 + 7573130 * 2 ^ 59
def prefixEnd_7573130 : Nat := 4983230072969 + 3 ^ 40 * 7573130 * 2
def baseEnd_7573130 : Nat := 1296218582994686775915605

theorem tailTrace_7573130 : CollatzResearch.WordTrace tailWord_7573130 prefixEnd_7573130 1296218582994686775915605 := by
  unfold tailWord_7573130
  simp only [CollatzResearch.WordTrace]
  refine ⟨69053685763462718119315211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184143162035900581651507229 69053685763462718119315211)
  ·
    refine ⟨103580528645194077178972817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69053685763462718119315211 103580528645194077178972817)
    ·
      refine ⟨77685396483895557884229613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103580528645194077178972817 77685396483895557884229613)
      ·
        refine ⟨29132023681460834206586105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77685396483895557884229613 29132023681460834206586105)
        ·
          refine ⟨21849017761095625654939579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29132023681460834206586105 21849017761095625654939579)
          ·
            refine ⟨32773526641643438482409369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21849017761095625654939579 32773526641643438482409369)
            ·
              refine ⟨24580144981232578861807027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32773526641643438482409369 24580144981232578861807027)
              ·
                refine ⟨36870217471848868292710541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24580144981232578861807027 36870217471848868292710541)
                ·
                  refine ⟨13826331551943325609766453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36870217471848868292710541 13826331551943325609766453)
                  ·
                    refine ⟨1296218582994686775915605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13826331551943325609766453 1296218582994686775915605)
                    ·
                      rfl

theorem cell23_7573130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_7573130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573130 prefixEnd_7573130 := by exact prefixLift 7573130
  have htrace : WordTrace (prefixWord ++ tailWord_7573130) baseStart_7573130 baseEnd_7573130 := by
    simpa [prefixWord, tailWord_7573130, baseEnd_7573130] using wordTrace_append hprefix tailTrace_7573130
  have hstable : (prefixWord ++ tailWord_7573130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573130).length < 2 ^ (prefixWord ++ tailWord_7573130).sum := by decide
  have hdescent : baseEnd_7573130 < baseStart_7573130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573144 : List Nat := [2, 1, 2, 4, 1, 2, 1, 5, 1, 1, 3]
def baseStart_7573144 : Nat := 118140960795 + 7573144 * 2 ^ 59
def prefixEnd_7573144 : Nat := 4983230072969 + 3 ^ 40 * 7573144 * 2
def baseEnd_7573144 : Nat := 3888662937713223272971751

theorem tailTrace_7573144 : CollatzResearch.WordTrace tailWord_7573144 prefixEnd_7573144 3888662937713223272971751 := by
  unfold tailWord_7573144
  simp only [CollatzResearch.WordTrace]
  refine ⟨138107626837900076434135243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184143502450533435245513657 138107626837900076434135243)
  ·
    refine ⟨207161440256850114651202865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138107626837900076434135243 207161440256850114651202865)
    ·
      refine ⟨155371080192637585988402149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207161440256850114651202865 155371080192637585988402149)
      ·
        refine ⟨29132077536119547372825403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155371080192637585988402149 29132077536119547372825403)
        ·
          refine ⟨43698116304179321059238105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29132077536119547372825403 43698116304179321059238105)
          ·
            refine ⟨32773587228134490794428579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43698116304179321059238105 32773587228134490794428579)
            ·
              refine ⟨49160380842201736191642869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32773587228134490794428579 49160380842201736191642869)
              ·
                refine ⟨4608785703956412767966519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49160380842201736191642869 4608785703956412767966519)
                ·
                  refine ⟨6913178555934619151949779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608785703956412767966519 6913178555934619151949779)
                  ·
                    refine ⟨10369767833901928727924669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6913178555934619151949779 10369767833901928727924669)
                    ·
                      refine ⟨3888662937713223272971751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369767833901928727924669 3888662937713223272971751)
                      ·
                        rfl

theorem cell23_7573144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_7573144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573144 prefixEnd_7573144 := by exact prefixLift 7573144
  have htrace : WordTrace (prefixWord ++ tailWord_7573144) baseStart_7573144 baseEnd_7573144 := by
    simpa [prefixWord, tailWord_7573144, baseEnd_7573144] using wordTrace_append hprefix tailTrace_7573144
  have hstable : (prefixWord ++ tailWord_7573144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573144).length < 2 ^ (prefixWord ++ tailWord_7573144).sum := by decide
  have hdescent : baseEnd_7573144 < baseStart_7573144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573170 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_7573170 : Nat := 118140960795 + 7573170 * 2 ^ 59
def prefixEnd_7573170 : Nat := 4983230072969 + 3 ^ 40 * 7573170 * 2
def baseEnd_7573170 : Nat := 3888676288210240171246631

theorem tailTrace_7573170 : CollatzResearch.WordTrace tailWord_7573170 prefixEnd_7573170 3888676288210240171246631 := by
  unfold tailWord_7573170
  simp only [CollatzResearch.WordTrace]
  refine ⟨69054050493426489827179241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184144134649137306205811309 69054050493426489827179241)
  ·
    refine ⟨51790537870069867370384431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69054050493426489827179241 51790537870069867370384431)
    ·
      refine ⟨77685806805104801055576647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51790537870069867370384431 77685806805104801055576647)
      ·
        refine ⟨116528710207657201583364971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77685806805104801055576647 116528710207657201583364971)
        ·
          refine ⟨174793065311485802375047457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116528710207657201583364971 174793065311485802375047457)
          ·
            refine ⟨131094798983614351781285593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174793065311485802375047457 131094798983614351781285593)
            ·
              refine ⟨98321099237710763835964195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131094798983614351781285593 98321099237710763835964195)
              ·
                refine ⟨147481648856566145753946293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98321099237710763835964195 147481648856566145753946293)
                ·
                  refine ⟨13826404580303076164432465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147481648856566145753946293 13826404580303076164432465)
                  ·
                    refine ⟨10369803435227307123324349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13826404580303076164432465 10369803435227307123324349)
                    ·
                      refine ⟨3888676288210240171246631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369803435227307123324349 3888676288210240171246631)
                      ·
                        rfl

theorem cell23_7573170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_7573170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573170 prefixEnd_7573170 := by exact prefixLift 7573170
  have htrace : WordTrace (prefixWord ++ tailWord_7573170) baseStart_7573170 baseEnd_7573170 := by
    simpa [prefixWord, tailWord_7573170, baseEnd_7573170] using wordTrace_append hprefix tailTrace_7573170
  have hstable : (prefixWord ++ tailWord_7573170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573170).length < 2 ^ (prefixWord ++ tailWord_7573170).sum := by decide
  have hdescent : baseEnd_7573170 < baseStart_7573170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573180 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_7573180 : Nat := 118140960795 + 7573180 * 2 ^ 59
def prefixEnd_7573180 : Nat := 4983230072969 + 3 ^ 40 * 7573180 * 2
def baseEnd_7573180 : Nat := 3888681423016785132121585

theorem tailTrace_7573180 : CollatzResearch.WordTrace tailWord_7573180 prefixEnd_7573180 3888681423016785132121585 := by
  unfold tailWord_7573180
  simp only [CollatzResearch.WordTrace]
  refine ⟨138108283351834865508290497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184144377802446487344387329 138108283351834865508290497)
  ·
    refine ⟨103581212513876149131217873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138108283351834865508290497 103581212513876149131217873)
    ·
      refine ⟨77685909385407111848413405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103581212513876149131217873 77685909385407111848413405)
      ·
        refine ⟨29132216019527666943155027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77685909385407111848413405 29132216019527666943155027)
        ·
          refine ⟨43698324029291500414732541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29132216019527666943155027 43698324029291500414732541)
          ·
            refine ⟨16386871510984312655524703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43698324029291500414732541 16386871510984312655524703)
            ·
              refine ⟨24580307266476468983287055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16386871510984312655524703 24580307266476468983287055)
              ·
                refine ⟨36870460899714703474930583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24580307266476468983287055 36870460899714703474930583)
                ·
                  refine ⟨55305691349572055212395875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36870460899714703474930583 55305691349572055212395875)
                  ·
                    refine ⟨82958537024358082818593813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55305691349572055212395875 82958537024358082818593813)
                    ·
                      refine ⟨3888681423016785132121585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82958537024358082818593813 3888681423016785132121585)
                      ·
                        rfl

theorem cell23_7573180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_7573180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573180 prefixEnd_7573180 := by exact prefixLift 7573180
  have htrace : WordTrace (prefixWord ++ tailWord_7573180) baseStart_7573180 baseEnd_7573180 := by
    simpa [prefixWord, tailWord_7573180, baseEnd_7573180] using wordTrace_append hprefix tailTrace_7573180
  have hstable : (prefixWord ++ tailWord_7573180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573180).length < 2 ^ (prefixWord ++ tailWord_7573180).sum := by decide
  have hdescent : baseEnd_7573180 < baseStart_7573180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573201 : List Nat := [1, 2, 2, 1, 2, 4, 3, 3, 1, 2, 2]
def baseStart_7573201 : Nat := 118140960795 + 7573201 * 2 ^ 59
def prefixEnd_7573201 : Nat := 4983230072969 + 3 ^ 40 * 7573201 * 2
def baseEnd_7573201 : Nat := 3888692206110529549958989

theorem tailTrace_7573201 : CollatzResearch.WordTrace tailWord_7573201 prefixEnd_7573201 3888692206110529549958989 := by
  unfold tailWord_7573201
  simp only [CollatzResearch.WordTrace]
  refine ⟨276217332636593651603095457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184144888424395767735396971 276217332636593651603095457)
  ·
    refine ⟨207162999477445238702321593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276217332636593651603095457 207162999477445238702321593)
    ·
      refine ⟨155372249608083929026741195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207162999477445238702321593 155372249608083929026741195)
      ·
        refine ⟨233058374412125893540111793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155372249608083929026741195 233058374412125893540111793)
        ·
          refine ⟨174793780809094420155083845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233058374412125893540111793 174793780809094420155083845)
          ·
            refine ⟨32773833901705203779078221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174793780809094420155083845 32773833901705203779078221)
            ·
              refine ⟨12290187713139451417154333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32773833901705203779078221 12290187713139451417154333)
              ·
                refine ⟨4608820392427294281432875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12290187713139451417154333 4608820392427294281432875)
                ·
                  refine ⟨6913230588640941422149313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608820392427294281432875 6913230588640941422149313)
                  ·
                    refine ⟨5184922941480706066611985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6913230588640941422149313 5184922941480706066611985)
                    ·
                      refine ⟨3888692206110529549958989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5184922941480706066611985 3888692206110529549958989)
                      ·
                        rfl

theorem cell23_7573201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_7573201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573201 prefixEnd_7573201 := by exact prefixLift 7573201
  have htrace : WordTrace (prefixWord ++ tailWord_7573201) baseStart_7573201 baseEnd_7573201 := by
    simpa [prefixWord, tailWord_7573201, baseEnd_7573201] using wordTrace_append hprefix tailTrace_7573201
  have hstable : (prefixWord ++ tailWord_7573201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573201).length < 2 ^ (prefixWord ++ tailWord_7573201).sum := by decide
  have hdescent : baseEnd_7573201 < baseStart_7573201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573204 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7573204 : Nat := 118140960795 + 7573204 * 2 ^ 59
def prefixEnd_7573204 : Nat := 4983230072969 + 3 ^ 40 * 7573204 * 2
def baseEnd_7573204 : Nat := 3888693746552493038221475

theorem tailTrace_7573204 : CollatzResearch.WordTrace tailWord_7573204 prefixEnd_7573204 3888693746552493038221475 := by
  unfold tailWord_7573204
  simp only [CollatzResearch.WordTrace]
  refine ⟨138108721027791391557727333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184144961370388522076969777 138108721027791391557727333)
  ·
    refine ⟨25895385192710885917073875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138108721027791391557727333 25895385192710885917073875)
    ·
      refine ⟨38843077789066328875610813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25895385192710885917073875 38843077789066328875610813)
      ·
        refine ⟨14566154170899873328354055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38843077789066328875610813 14566154170899873328354055)
        ·
          refine ⟨21849231256349809992531083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14566154170899873328354055 21849231256349809992531083)
          ·
            refine ⟨32773846884524714988796625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21849231256349809992531083 32773846884524714988796625)
            ·
              refine ⟨24580385163393536241597469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32773846884524714988796625 24580385163393536241597469)
              ·
                refine ⟨9217644436272576090599051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24580385163393536241597469 9217644436272576090599051)
                ·
                  refine ⟨13826466654408864135898577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9217644436272576090599051 13826466654408864135898577)
                  ·
                    refine ⟨10369849990806648101923933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13826466654408864135898577 10369849990806648101923933)
                    ·
                      refine ⟨3888693746552493038221475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369849990806648101923933 3888693746552493038221475)
                      ·
                        rfl

theorem cell23_7573204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7573204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573204 prefixEnd_7573204 := by exact prefixLift 7573204
  have htrace : WordTrace (prefixWord ++ tailWord_7573204) baseStart_7573204 baseEnd_7573204 := by
    simpa [prefixWord, tailWord_7573204, baseEnd_7573204] using wordTrace_append hprefix tailTrace_7573204
  have hstable : (prefixWord ++ tailWord_7573204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573204).length < 2 ^ (prefixWord ++ tailWord_7573204).sum := by decide
  have hdescent : baseEnd_7573204 < baseStart_7573204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573234 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_7573234 : Nat := 118140960795 + 7573234 * 2 ^ 59
def prefixEnd_7573234 : Nat := 4983230072969 + 3 ^ 40 * 7573234 * 2
def baseEnd_7573234 : Nat := 3888709150972127920846337

theorem tailTrace_7573234 : CollatzResearch.WordTrace tailWord_7573234 prefixEnd_7573234 3888709150972127920846337 := by
  unfold tailWord_7573234
  simp only [CollatzResearch.WordTrace]
  refine ⟨69054634061368524559761689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184145690830316065492697837 69054634061368524559761689)
  ·
    refine ⟨51790975546026393419821267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69054634061368524559761689 51790975546026393419821267)
    ·
      refine ⟨77686463319039590129731901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51790975546026393419821267 77686463319039590129731901)
      ·
        refine ⟨29132423744639846298649463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77686463319039590129731901 29132423744639846298649463)
        ·
          refine ⟨43698635616959769447974195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29132423744639846298649463 43698635616959769447974195)
          ·
            refine ⟨65547953425439654171961293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43698635616959769447974195 65547953425439654171961293)
            ·
              refine ⟨24580482534539870314485485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65547953425439654171961293 24580482534539870314485485)
              ·
                refine ⟨9217680950452451367932057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24580482534539870314485485 9217680950452451367932057)
                ·
                  refine ⟨6913260712839338525949043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9217680950452451367932057 6913260712839338525949043)
                  ·
                    refine ⟨10369891069259007788923565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6913260712839338525949043 10369891069259007788923565)
                    ·
                      refine ⟨3888709150972127920846337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10369891069259007788923565 3888709150972127920846337)
                      ·
                        rfl

theorem cell23_7573234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_7573234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573234 prefixEnd_7573234 := by exact prefixLift 7573234
  have htrace : WordTrace (prefixWord ++ tailWord_7573234) baseStart_7573234 baseEnd_7573234 := by
    simpa [prefixWord, tailWord_7573234, baseEnd_7573234] using wordTrace_append hprefix tailTrace_7573234
  have hstable : (prefixWord ++ tailWord_7573234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573234).length < 2 ^ (prefixWord ++ tailWord_7573234).sum := by decide
  have hdescent : baseEnd_7573234 < baseStart_7573234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573260 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_7573260 : Nat := 118140960795 + 7573260 * 2 ^ 59
def prefixEnd_7573260 : Nat := 4983230072969 + 3 ^ 40 * 7573260 * 2
def baseEnd_7573260 : Nat := 3888722501469144819121217

theorem tailTrace_7573260 : CollatzResearch.WordTrace tailWord_7573260 prefixEnd_7573260 3888722501469144819121217 := by
  unfold tailWord_7573260
  simp only [CollatzResearch.WordTrace]
  refine ⟨138109742271689952339746617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184146323028919936452995489 138109742271689952339746617)
  ·
    refine ⟨103582306703767464254809963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138109742271689952339746617 103582306703767464254809963)
    ·
      refine ⟨155373460055651196382214945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103582306703767464254809963 155373460055651196382214945)
      ·
        refine ⟨116530095041738397286661209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155373460055651196382214945 116530095041738397286661209)
        ·
          refine ⟨87397571281303797964995907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116530095041738397286661209 87397571281303797964995907)
          ·
            refine ⟨131096356921955696947493861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87397571281303797964995907 131096356921955696947493861)
            ·
              refine ⟨24580566922866693177655099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131096356921955696947493861 24580566922866693177655099)
              ·
                refine ⟨36870850384300039766482649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24580566922866693177655099 36870850384300039766482649)
                ·
                  refine ⟨27653137788225029824861987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36870850384300039766482649 27653137788225029824861987)
                  ·
                    refine ⟨41479706682337544737292981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27653137788225029824861987 41479706682337544737292981)
                    ·
                      refine ⟨3888722501469144819121217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41479706682337544737292981 3888722501469144819121217)
                      ·
                        rfl

theorem cell23_7573260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_7573260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573260 prefixEnd_7573260 := by exact prefixLift 7573260
  have htrace : WordTrace (prefixWord ++ tailWord_7573260) baseStart_7573260 baseEnd_7573260 := by
    simpa [prefixWord, tailWord_7573260, baseEnd_7573260] using wordTrace_append hprefix tailTrace_7573260
  have hstable : (prefixWord ++ tailWord_7573260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573260).length < 2 ^ (prefixWord ++ tailWord_7573260).sum := by decide
  have hdescent : baseEnd_7573260 < baseStart_7573260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573263 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 11]
def baseStart_7573263 : Nat := 118140960795 + 7573263 * 2 ^ 59
def prefixEnd_7573263 : Nat := 4983230072969 + 3 ^ 40 * 7573263 * 2
def baseEnd_7573263 : Nat := 432080449101234256375967

theorem tailTrace_7573263 : CollatzResearch.WordTrace tailWord_7573263 prefixEnd_7573263 432080449101234256375967 := by
  unfold tailWord_7573263
  simp only [CollatzResearch.WordTrace]
  refine ⟨276219593962369036191852443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184146395974912690794568295 276219593962369036191852443)
  ·
    refine ⟨414329390943553554287778665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276219593962369036191852443 414329390943553554287778665)
    ·
      refine ⟨310747043207665165715833999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414329390943553554287778665 310747043207665165715833999)
      ·
        refine ⟨466120564811497748573750999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310747043207665165715833999 466120564811497748573750999)
        ·
          refine ⟨699180847217246622860626499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466120564811497748573750999 699180847217246622860626499)
          ·
            refine ⟨1048771270825869934290939749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699180847217246622860626499 1048771270825869934290939749)
            ·
              refine ⟨196644613279850612679551203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1048771270825869934290939749 196644613279850612679551203)
              ·
                refine ⟨294966919919775919019326805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196644613279850612679551203 294966919919775919019326805)
                ·
                  refine ⟨432080449101234256375967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 294966919919775919019326805 432080449101234256375967)
                  ·
                    rfl

theorem cell23_7573263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 11].length) (baseStart_7573263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573263 prefixEnd_7573263 := by exact prefixLift 7573263
  have htrace : WordTrace (prefixWord ++ tailWord_7573263) baseStart_7573263 baseEnd_7573263 := by
    simpa [prefixWord, tailWord_7573263, baseEnd_7573263] using wordTrace_append hprefix tailTrace_7573263
  have hstable : (prefixWord ++ tailWord_7573263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573263).length < 2 ^ (prefixWord ++ tailWord_7573263).sum := by decide
  have hdescent : baseEnd_7573263 < baseStart_7573263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573280 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 7]
def baseStart_7573280 : Nat := 118140960795 + 7573280 * 2 ^ 59
def prefixEnd_7573280 : Nat := 4983230072969 + 3 ^ 40 * 7573280 * 2
def baseEnd_7573280 : Nat := 432081419009137193430125

theorem tailTrace_7573280 : CollatzResearch.WordTrace tailWord_7573280 prefixEnd_7573280 432081419009137193430125 := by
  unfold tailWord_7573280
  simp only [CollatzResearch.WordTrace]
  refine ⟨138110107001653724047610647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184146809335538298730147529 138110107001653724047610647)
  ·
    refine ⟨207165160502480586071415971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138110107001653724047610647 207165160502480586071415971)
    ·
      refine ⟨310747740753720879107123957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207165160502480586071415971 310747740753720879107123957)
      ·
        refine ⟨29132600695661332416292871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 310747740753720879107123957 29132600695661332416292871)
        ·
          refine ⟨43698901043491998624439307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29132600695661332416292871 43698901043491998624439307)
          ·
            refine ⟨65548351565237997936658961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43698901043491998624439307 65548351565237997936658961)
            ·
              refine ⟨49161263673928498452494221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65548351565237997936658961 49161263673928498452494221)
              ·
                refine ⟨18435473877723186919685333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49161263673928498452494221 18435473877723186919685333)
                ·
                  refine ⟨432081419009137193430125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18435473877723186919685333 432081419009137193430125)
                  ·
                    rfl

theorem cell23_7573280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 7].length) (baseStart_7573280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573280 prefixEnd_7573280 := by exact prefixLift 7573280
  have htrace : WordTrace (prefixWord ++ tailWord_7573280) baseStart_7573280 baseEnd_7573280 := by
    simpa [prefixWord, tailWord_7573280, baseEnd_7573280] using wordTrace_append hprefix tailTrace_7573280
  have hstable : (prefixWord ++ tailWord_7573280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573280).length < 2 ^ (prefixWord ++ tailWord_7573280).sum := by decide
  have hdescent : baseEnd_7573280 < baseStart_7573280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573325 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7573325 : Nat := 118140960795 + 7573325 * 2 ^ 59
def prefixEnd_7573325 : Nat := 4983230072969 + 3 ^ 40 * 7573325 * 2
def baseEnd_7573325 : Nat := 3888755877711687064808419

theorem tailTrace_7573325 : CollatzResearch.WordTrace tailWord_7573325 prefixEnd_7573325 3888755877711687064808419 := by
  unfold tailWord_7573325
  simp only [CollatzResearch.WordTrace]
  refine ⟨276221855288144420780609429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184147903525429613853739619 276221855288144420780609429)
  ·
    refine ⟨12947899466631769724091067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 276221855288144420780609429 12947899466631769724091067)
    ·
      refine ⟨19421849199947654586136601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12947899466631769724091067 19421849199947654586136601)
      ·
        refine ⟨14566386899960740939602451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19421849199947654586136601 14566386899960740939602451)
        ·
          refine ⟨21849580349941111409403677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14566386899960740939602451 21849580349941111409403677)
          ·
            refine ⟨8193592631227916778526379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21849580349941111409403677 8193592631227916778526379)
            ·
              refine ⟨12290388946841875167789569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8193592631227916778526379 12290388946841875167789569)
              ·
                refine ⟨9217791710131406375842177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12290388946841875167789569 9217791710131406375842177)
                ·
                  refine ⟨6913343782598554781881633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9217791710131406375842177 6913343782598554781881633)
                  ·
                    refine ⟨5185007836948916086411225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6913343782598554781881633 5185007836948916086411225)
                    ·
                      refine ⟨3888755877711687064808419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185007836948916086411225 3888755877711687064808419)
                      ·
                        rfl

theorem cell23_7573325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7573325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573325 prefixEnd_7573325 := by exact prefixLift 7573325
  have htrace : WordTrace (prefixWord ++ tailWord_7573325) baseStart_7573325 baseEnd_7573325 := by
    simpa [prefixWord, tailWord_7573325, baseEnd_7573325] using wordTrace_append hprefix tailTrace_7573325
  have hstable : (prefixWord ++ tailWord_7573325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573325).length < 2 ^ (prefixWord ++ tailWord_7573325).sum := by decide
  have hdescent : baseEnd_7573325 < baseStart_7573325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573360 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_7573360 : Nat := 118140960795 + 7573360 * 2 ^ 59
def prefixEnd_7573360 : Nat := 4983230072969 + 3 ^ 40 * 7573360 * 2
def baseEnd_7573360 : Nat := 3888773849534594427870757

theorem tailTrace_7573360 : CollatzResearch.WordTrace tailWord_7573360 prefixEnd_7573360 3888773849534594427870757 := by
  unfold tailWord_7573360
  simp only [CollatzResearch.WordTrace]
  refine ⟨138111565921508810879066767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184148754562011747838755689 138111565921508810879066767)
  ·
    refine ⟨207167348882263216318600151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138111565921508810879066767 207167348882263216318600151)
    ·
      refine ⟨310751023323394824477900227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207167348882263216318600151 310751023323394824477900227)
      ·
        refine ⟨466126534985092236716850341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310751023323394824477900227 466126534985092236716850341)
        ·
          refine ⟨87398725309704794384409439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466126534985092236716850341 87398725309704794384409439)
          ·
            refine ⟨131098087964557191576614159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87398725309704794384409439 131098087964557191576614159)
            ·
              refine ⟨196647131946835787364921239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131098087964557191576614159 196647131946835787364921239)
              ·
                refine ⟨294970697920253681047381859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196647131946835787364921239 294970697920253681047381859)
                ·
                  refine ⟨442456046880380521571072789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294970697920253681047381859 442456046880380521571072789)
                  ·
                    refine ⟨20740127197517836948644037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 442456046880380521571072789 20740127197517836948644037)
                    ·
                      refine ⟨3888773849534594427870757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20740127197517836948644037 3888773849534594427870757)
                      ·
                        rfl

theorem cell23_7573360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_7573360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573360 prefixEnd_7573360 := by exact prefixLift 7573360
  have htrace : WordTrace (prefixWord ++ tailWord_7573360) baseStart_7573360 baseEnd_7573360 := by
    simpa [prefixWord, tailWord_7573360, baseEnd_7573360] using wordTrace_append hprefix tailTrace_7573360
  have hstable : (prefixWord ++ tailWord_7573360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573360).length < 2 ^ (prefixWord ++ tailWord_7573360).sum := by decide
  have hdescent : baseEnd_7573360 < baseStart_7573360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573370 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 8]
def baseStart_7573370 : Nat := 118140960795 + 7573370 * 2 ^ 59
def prefixEnd_7573370 : Nat := 4983230072969 + 3 ^ 40 * 7573370 * 2
def baseEnd_7573370 : Nat := 432086553815682154305079

theorem tailTrace_7573370 : CollatzResearch.WordTrace tailWord_7573370 prefixEnd_7573370 432086553815682154305079 := by
  unfold tailWord_7573370
  simp only [CollatzResearch.WordTrace]
  refine ⟨69055874143245348366499391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184148997715320928977331709 69055874143245348366499391)
  ·
    refine ⟨103583811214868022549749087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69055874143245348366499391 103583811214868022549749087)
    ·
      refine ⟨155375716822302033824623631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103583811214868022549749087 155375716822302033824623631)
      ·
        refine ⟨233063575233453050736935447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155375716822302033824623631 233063575233453050736935447)
        ·
          refine ⟨349595362850179576105403171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233063575233453050736935447 349595362850179576105403171)
          ·
            refine ⟨524393044275269364158104757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349595362850179576105403171 524393044275269364158104757)
            ·
              refine ⟨49161847900806502889822321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 524393044275269364158104757 49161847900806502889822321)
              ·
                refine ⟨36871385925604877167366741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49161847900806502889822321 36871385925604877167366741)
                ·
                  refine ⟨432086553815682154305079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36871385925604877167366741 432086553815682154305079)
                  ·
                    rfl

theorem cell23_7573370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_7573370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573370 prefixEnd_7573370 := by exact prefixLift 7573370
  have htrace : WordTrace (prefixWord ++ tailWord_7573370) baseStart_7573370 baseEnd_7573370 := by
    simpa [prefixWord, tailWord_7573370, baseEnd_7573370] using wordTrace_append hprefix tailTrace_7573370
  have hstable : (prefixWord ++ tailWord_7573370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573370).length < 2 ^ (prefixWord ++ tailWord_7573370).sum := by decide
  have hdescent : baseEnd_7573370 < baseStart_7573370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573404 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 6]
def baseStart_7573404 : Nat := 118140960795 + 7573404 * 2 ^ 59
def prefixEnd_7573404 : Nat := 4983230072969 + 3 ^ 40 * 7573404 * 2
def baseEnd_7573404 : Nat := 432088493631488028413395

theorem tailTrace_7573404 : CollatzResearch.WordTrace tailWord_7573404 prefixEnd_7573404 432088493631488028413395 := by
  unfold tailWord_7573404
  simp only [CollatzResearch.WordTrace]
  refine ⟨138112368327429108636367633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184149824436572144848490177 138112368327429108636367633)
  ·
    refine ⟨103584276245571831477275725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138112368327429108636367633 103584276245571831477275725)
    ·
      refine ⟨38844103592089436803978397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103584276245571831477275725 38844103592089436803978397)
      ·
        refine ⟨14566538847033538801491899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38844103592089436803978397 14566538847033538801491899)
        ·
          refine ⟨21849808270550308202237849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14566538847033538801491899 21849808270550308202237849)
          ·
            refine ⟨16387356202912731151678387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21849808270550308202237849 16387356202912731151678387)
            ·
              refine ⟨24581034304369096727517581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16387356202912731151678387 24581034304369096727517581)
              ·
                refine ⟨9217887864138411272819093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24581034304369096727517581 9217887864138411272819093)
                ·
                  refine ⟨432088493631488028413395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9217887864138411272819093 432088493631488028413395)
                  ·
                    rfl

theorem cell23_7573404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_7573404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573404 prefixEnd_7573404 := by exact prefixLift 7573404
  have htrace : WordTrace (prefixWord ++ tailWord_7573404) baseStart_7573404 baseEnd_7573404 := by
    simpa [prefixWord, tailWord_7573404, baseEnd_7573404] using wordTrace_append hprefix tailTrace_7573404
  have hstable : (prefixWord ++ tailWord_7573404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573404).length < 2 ^ (prefixWord ++ tailWord_7573404).sum := by decide
  have hdescent : baseEnd_7573404 < baseStart_7573404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573417 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 1, 5]
def baseStart_7573417 : Nat := 118140960795 + 7573417 * 2 ^ 59
def prefixEnd_7573417 : Nat := 4983230072969 + 3 ^ 40 * 7573417 * 2
def baseEnd_7573417 : Nat := 1296267705977300234952665

theorem tailTrace_7573417 : CollatzResearch.WordTrace tailWord_7573417 prefixEnd_7573417 1296267705977300234952665 := by
  unfold tailWord_7573417
  simp only [CollatzResearch.WordTrace]
  refine ⟨276225210803811120492958505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184150140535874080328639003 276225210803811120492958505)
  ·
    refine ⟨207168908102858340369718879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276225210803811120492958505 207168908102858340369718879)
    ·
      refine ⟨310753362154287510554578319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207168908102858340369718879 310753362154287510554578319)
      ·
        refine ⟨466130043231431265831867479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310753362154287510554578319 466130043231431265831867479)
        ·
          refine ⟨699195064847146898747801219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466130043231431265831867479 699195064847146898747801219)
          ·
            refine ⟨1048792597270720348121701829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699195064847146898747801219 1048792597270720348121701829)
            ·
              refine ⟨196648611988260065272819093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1048792597270720348121701829 196648611988260065272819093)
              ·
                refine ⟨9217903686949690559663395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196648611988260065272819093 9217903686949690559663395)
                ·
                  refine ⟨13826855530424535839495093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9217903686949690559663395 13826855530424535839495093)
                  ·
                    refine ⟨1296267705977300234952665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13826855530424535839495093 1296267705977300234952665)
                    ·
                      rfl

theorem cell23_7573417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_7573417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573417 prefixEnd_7573417 := by exact prefixLift 7573417
  have htrace : WordTrace (prefixWord ++ tailWord_7573417) baseStart_7573417 baseEnd_7573417 := by
    simpa [prefixWord, tailWord_7573417, baseEnd_7573417] using wordTrace_append hprefix tailTrace_7573417
  have hstable : (prefixWord ++ tailWord_7573417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573417).length < 2 ^ (prefixWord ++ tailWord_7573417).sum := by decide
  have hdescent : baseEnd_7573417 < baseStart_7573417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573431 : List Nat := [1, 1, 3, 1, 3, 1, 1, 7, 1, 1, 3]
def baseStart_7573431 : Nat := 118140960795 + 7573431 * 2 ^ 59
def prefixEnd_7573431 : Nat := 4983230072969 + 3 ^ 40 * 7573431 * 2
def baseEnd_7573431 : Nat := 3888810306661063650082931

theorem tailTrace_7573431 : CollatzResearch.WordTrace tailWord_7573431 prefixEnd_7573431 3888810306661063650082931 := by
  unfold tailWord_7573431
  simp only [CollatzResearch.WordTrace]
  refine ⟨276225721425760400883968147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184150480950506933922645431 276225721425760400883968147)
  ·
    refine ⟨414338582138640601325952221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276225721425760400883968147 414338582138640601325952221)
    ·
      refine ⟨155376968301990225497232083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414338582138640601325952221 155376968301990225497232083)
      ·
        refine ⟨233065452452985338245848125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155376968301990225497232083 233065452452985338245848125)
        ·
          refine ⟨87399544669869501842193047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233065452452985338245848125 87399544669869501842193047)
          ·
            refine ⟨131099317004804252763289571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87399544669869501842193047 131099317004804252763289571)
            ·
              refine ⟨196648975507206379144934357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131099317004804252763289571 196648975507206379144934357)
              ·
                refine ⟨4608960363450149511209399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 196648975507206379144934357 4608960363450149511209399)
                ·
                  refine ⟨6913440545175224266814099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608960363450149511209399 6913440545175224266814099)
                  ·
                    refine ⟨10370160817762836400221149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6913440545175224266814099 10370160817762836400221149)
                    ·
                      refine ⟨3888810306661063650082931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10370160817762836400221149 3888810306661063650082931)
                      ·
                        rfl

theorem cell23_7573431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_7573431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573431 prefixEnd_7573431 := by exact prefixLift 7573431
  have htrace : WordTrace (prefixWord ++ tailWord_7573431) baseStart_7573431 baseEnd_7573431 := by
    simpa [prefixWord, tailWord_7573431, baseEnd_7573431] using wordTrace_append hprefix tailTrace_7573431
  have hstable : (prefixWord ++ tailWord_7573431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573431).length < 2 ^ (prefixWord ++ tailWord_7573431).sum := by decide
  have hdescent : baseEnd_7573431 < baseStart_7573431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573448 : List Nat := [2, 1, 3, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_7573448 : Nat := 118140960795 + 7573448 * 2 ^ 59
def prefixEnd_7573448 : Nat := 4983230072969 + 3 ^ 40 * 7573448 * 2
def baseEnd_7573448 : Nat := 3888819035832190083570353

theorem tailTrace_7573448 : CollatzResearch.WordTrace tailWord_7573448 prefixEnd_7573448 3888819035832190083570353 := by
  unfold tailWord_7573448
  simp only [CollatzResearch.WordTrace]
  refine ⟨138113170733349406393668499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184150894311132541858224665 138113170733349406393668499)
  ·
    refine ⟨207169756100024109590502749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138113170733349406393668499 207169756100024109590502749)
    ·
      refine ⟨77688658537509041096438531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207169756100024109590502749 77688658537509041096438531)
      ·
        refine ⟨116532987806263561644657797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77688658537509041096438531 116532987806263561644657797)
        ·
          refine ⟨21849935213674417808373337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116532987806263561644657797 21849935213674417808373337)
          ·
            refine ⟨16387451410255813356280003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21849935213674417808373337 16387451410255813356280003)
            ·
              refine ⟨24581177115383720034420005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16387451410255813356280003 24581177115383720034420005)
              ·
                refine ⟨4608970709134447506453751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24581177115383720034420005 4608970709134447506453751)
                ·
                  refine ⟨6913456063701671259680627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608970709134447506453751 6913456063701671259680627)
                  ·
                    refine ⟨10370184095552506889520941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6913456063701671259680627 10370184095552506889520941)
                    ·
                      refine ⟨3888819035832190083570353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10370184095552506889520941 3888819035832190083570353)
                      ·
                        rfl

theorem cell23_7573448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_7573448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573448 prefixEnd_7573448 := by exact prefixLift 7573448
  have htrace : WordTrace (prefixWord ++ tailWord_7573448) baseStart_7573448 baseEnd_7573448 := by
    simpa [prefixWord, tailWord_7573448, baseEnd_7573448] using wordTrace_append hprefix tailTrace_7573448
  have hstable : (prefixWord ++ tailWord_7573448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573448).length < 2 ^ (prefixWord ++ tailWord_7573448).sum := by decide
  have hdescent : baseEnd_7573448 < baseStart_7573448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573464 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 2, 4]
def baseStart_7573464 : Nat := 118140960795 + 7573464 * 2 ^ 59
def prefixEnd_7573464 : Nat := 4983230072969 + 3 ^ 40 * 7573464 * 2
def baseEnd_7573464 : Nat := 1296275750507554006990093

theorem tailTrace_7573464 : CollatzResearch.WordTrace tailWord_7573464 prefixEnd_7573464 1296275750507554006990093 := by
  unfold tailWord_7573464
  simp only [CollatzResearch.WordTrace]
  refine ⟨138113462517320423759959723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184151283356427231679946297 138113462517320423759959723)
  ·
    refine ⟨207170193775980635639939585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138113462517320423759959723 207170193775980635639939585)
    ·
      refine ⟨155377645331985476729954689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207170193775980635639939585 155377645331985476729954689)
      ·
        refine ⟨116533233998989107547466017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155377645331985476729954689 116533233998989107547466017)
        ·
          refine ⟨87399925499241830660599513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116533233998989107547466017 87399925499241830660599513)
          ·
            refine ⟨65549944124431372995449635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87399925499241830660599513 65549944124431372995449635)
            ·
              refine ⟨98324916186647059493174453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65549944124431372995449635 98324916186647059493174453)
              ·
                refine ⟨9217960892498161827485105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98324916186647059493174453 9217960892498161827485105)
                ·
                  refine ⟨6913470669373621370613829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9217960892498161827485105 6913470669373621370613829)
                  ·
                    refine ⟨1296275750507554006990093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6913470669373621370613829 1296275750507554006990093)
                    ·
                      rfl

theorem cell23_7573464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_7573464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573464 prefixEnd_7573464 := by exact prefixLift 7573464
  have htrace : WordTrace (prefixWord ++ tailWord_7573464) baseStart_7573464 baseEnd_7573464 := by
    simpa [prefixWord, tailWord_7573464, baseEnd_7573464] using wordTrace_append hprefix tailTrace_7573464
  have hstable : (prefixWord ++ tailWord_7573464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573464).length < 2 ^ (prefixWord ++ tailWord_7573464).sum := by decide
  have hdescent : baseEnd_7573464 < baseStart_7573464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573471 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 5, 2, 2]
def baseStart_7573471 : Nat := 118140960795 + 7573471 * 2 ^ 59
def prefixEnd_7573471 : Nat := 4983230072969 + 3 ^ 40 * 7573471 * 2
def baseEnd_7573471 : Nat := 3888830845887243493582747

theorem tailTrace_7573471 : CollatzResearch.WordTrace tailWord_7573471 prefixEnd_7573471 3888830845887243493582747 := by
  unfold tailWord_7573471
  simp only [CollatzResearch.WordTrace]
  refine ⟨276227180345615487715424267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184151453563743658476949511 276227180345615487715424267)
  ·
    refine ⟨414340770518423231573136401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276227180345615487715424267 414340770518423231573136401)
    ·
      refine ⟨310755577888817423679852301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414340770518423231573136401 310755577888817423679852301)
      ·
        refine ⟨116533341708306533879944613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310755577888817423679852301 116533341708306533879944613)
        ·
          refine ⟨21850001570307475102489615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116533341708306533879944613 21850001570307475102489615)
          ·
            refine ⟨32775002355461212653734423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21850001570307475102489615 32775002355461212653734423)
            ·
              refine ⟨49162503533191818980601635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32775002355461212653734423 49162503533191818980601635)
              ·
                refine ⟨73743755299787728470902453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49162503533191818980601635 73743755299787728470902453)
                ·
                  refine ⟨6913477059355099544147105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73743755299787728470902453 6913477059355099544147105)
                  ·
                    refine ⟨5185107794516324658110329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6913477059355099544147105 5185107794516324658110329)
                    ·
                      refine ⟨3888830845887243493582747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185107794516324658110329 3888830845887243493582747)
                      ·
                        rfl

theorem cell23_7573471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_7573471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573471 prefixEnd_7573471 := by exact prefixLift 7573471
  have htrace : WordTrace (prefixWord ++ tailWord_7573471) baseStart_7573471 baseEnd_7573471 := by
    simpa [prefixWord, tailWord_7573471, baseEnd_7573471] using wordTrace_append hprefix tailTrace_7573471
  have hstable : (prefixWord ++ tailWord_7573471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573471).length < 2 ^ (prefixWord ++ tailWord_7573471).sum := by decide
  have hdescent : baseEnd_7573471 < baseStart_7573471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573485 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_7573485 : Nat := 118140960795 + 7573485 * 2 ^ 59
def prefixEnd_7573485 : Nat := 4983230072969 + 3 ^ 40 * 7573485 * 2
def baseEnd_7573485 : Nat := 1296279344872135479602561

theorem tailTrace_7573485 : CollatzResearch.WordTrace tailWord_7573485 prefixEnd_7573485 1296279344872135479602561 := by
  unfold tailWord_7573485
  simp only [CollatzResearch.WordTrace]
  refine ⟨276227690967564768106433909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184151793978376512070955939 276227690967564768106433909)
  ·
    refine ⟨25896346028209197009978179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276227690967564768106433909 25896346028209197009978179)
    ·
      refine ⟨38844519042313795514967269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25896346028209197009978179 38844519042313795514967269)
      ·
        refine ⟨7283347320433836659056363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38844519042313795514967269 7283347320433836659056363)
        ·
          refine ⟨10925020980650754988584545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7283347320433836659056363 10925020980650754988584545)
          ·
            refine ⟨8193765735488066241438409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10925020980650754988584545 8193765735488066241438409)
            ·
              refine ⟨6145324301616049681078807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8193765735488066241438409 6145324301616049681078807)
              ·
                refine ⟨9217986452424074521618211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145324301616049681078807 9217986452424074521618211)
                ·
                  refine ⟨13826979678636111782427317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9217986452424074521618211 13826979678636111782427317)
                  ·
                    refine ⟨1296279344872135479602561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13826979678636111782427317 1296279344872135479602561)
                    ·
                      rfl

theorem cell23_7573485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_7573485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573485 prefixEnd_7573485 := by exact prefixLift 7573485
  have htrace : WordTrace (prefixWord ++ tailWord_7573485) baseStart_7573485 baseEnd_7573485 := by
    simpa [prefixWord, tailWord_7573485, baseEnd_7573485] using wordTrace_append hprefix tailTrace_7573485
  have hstable : (prefixWord ++ tailWord_7573485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573485).length < 2 ^ (prefixWord ++ tailWord_7573485).sum := by decide
  have hdescent : baseEnd_7573485 < baseStart_7573485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573488 : List Nat := [2, 1, 1, 1, 3, 2, 3, 5, 1, 2, 2]
def baseStart_7573488 : Nat := 118140960795 + 7573488 * 2 ^ 59
def prefixEnd_7573488 : Nat := 4983230072969 + 3 ^ 40 * 7573488 * 2
def baseEnd_7573488 : Nat := 3888839575058369927070169

theorem tailTrace_7573488 : CollatzResearch.WordTrace tailWord_7573488 prefixEnd_7573488 3888839575058369927070169 := by
  unfold tailWord_7573488
  simp only [CollatzResearch.WordTrace]
  refine ⟨138113900193276949809396559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184151866924369266412528745 138113900193276949809396559)
  ·
    refine ⟨207170850289915424714094839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138113900193276949809396559 207170850289915424714094839)
    ·
      refine ⟨310756275434873137071142259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207170850289915424714094839 310756275434873137071142259)
      ·
        refine ⟨466134413152309705606713389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310756275434873137071142259 466134413152309705606713389)
        ·
          refine ⟨174800404932116139602517521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466134413152309705606713389 174800404932116139602517521)
          ·
            refine ⟨131100303699087104701888141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174800404932116139602517521 131100303699087104701888141)
            ·
              refine ⟨49162613887157664263208053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131100303699087104701888141 49162613887157664263208053)
              ·
                refine ⟨4608995051921031024675755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49162613887157664263208053 4608995051921031024675755)
                ·
                  refine ⟨6913492577881546537013633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608995051921031024675755 6913492577881546537013633)
                  ·
                    refine ⟨5185119433411159902760225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6913492577881546537013633 5185119433411159902760225)
                    ·
                      refine ⟨3888839575058369927070169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185119433411159902760225 3888839575058369927070169)
                      ·
                        rfl

theorem cell23_7573488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 2, 2].length) (baseStart_7573488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573488 prefixEnd_7573488 := by exact prefixLift 7573488
  have htrace : WordTrace (prefixWord ++ tailWord_7573488) baseStart_7573488 baseEnd_7573488 := by
    simpa [prefixWord, tailWord_7573488, baseEnd_7573488] using wordTrace_append hprefix tailTrace_7573488
  have hstable : (prefixWord ++ tailWord_7573488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573488).length < 2 ^ (prefixWord ++ tailWord_7573488).sum := by decide
  have hdescent : baseEnd_7573488 < baseStart_7573488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573494 : List Nat := [5, 1, 1, 1, 4, 1, 10]
def baseStart_7573494 : Nat := 118140960795 + 7573494 * 2 ^ 59
def prefixEnd_7573494 : Nat := 4983230072969 + 3 ^ 40 * 7573494 * 2
def baseEnd_7573494 : Nat := 48010403159781443254261

theorem tailTrace_7573494 : CollatzResearch.WordTrace tailWord_7573494 prefixEnd_7573494 48010403159781443254261 := by
  unfold tailWord_7573494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17264251201533260165219471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184152012816354775095674357 17264251201533260165219471)
  ·
    refine ⟨25896376802299890247829207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17264251201533260165219471 25896376802299890247829207)
    ·
      refine ⟨38844565203449835371743811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25896376802299890247829207 38844565203449835371743811)
      ·
        refine ⟨58266847805174753057615717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38844565203449835371743811 58266847805174753057615717)
        ·
          refine ⟨10925033963470266198302947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58266847805174753057615717 10925033963470266198302947)
          ·
            refine ⟨16387550945205399297454421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10925033963470266198302947 16387550945205399297454421)
            ·
              refine ⟨48010403159781443254261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16387550945205399297454421 48010403159781443254261)
              ·
                rfl

theorem cell23_7573494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 10].length) (baseStart_7573494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573494 prefixEnd_7573494 := by exact prefixLift 7573494
  have htrace : WordTrace (prefixWord ++ tailWord_7573494) baseStart_7573494 baseEnd_7573494 := by
    simpa [prefixWord, tailWord_7573494, baseEnd_7573494] using wordTrace_append hprefix tailTrace_7573494
  have hstable : (prefixWord ++ tailWord_7573494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573494).length < 2 ^ (prefixWord ++ tailWord_7573494).sum := by decide
  have hdescent : baseEnd_7573494 < baseStart_7573494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573564 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_7573564 : Nat := 118140960795 + 7573564 * 2 ^ 59
def prefixEnd_7573564 : Nat := 4983230072969 + 3 ^ 40 * 7573564 * 2
def baseEnd_7573564 : Nat := 3888878599588111629719819

theorem tailTrace_7573564 : CollatzResearch.WordTrace tailWord_7573564 prefixEnd_7573564 3888878599588111629719819 := by
  unfold tailWord_7573564
  simp only [CollatzResearch.WordTrace]
  refine ⟨138115286167139282299279873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184153714889519043065706497 138115286167139282299279873)
  ·
    refine ⟨103586464625354461724459905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138115286167139282299279873 103586464625354461724459905)
    ·
      refine ⟨77689848469015846293344929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103586464625354461724459905 77689848469015846293344929)
      ·
        refine ⟨58267386351761884720008697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77689848469015846293344929 58267386351761884720008697)
        ·
          refine ⟨43700539763821413540006523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58267386351761884720008697 43700539763821413540006523)
          ·
            refine ⟨65550809645732120310009785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43700539763821413540006523 65550809645732120310009785)
            ·
              refine ⟨49163107234299090232507339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65550809645732120310009785 49163107234299090232507339)
              ·
                refine ⟨73744660851448635348761009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49163107234299090232507339 73744660851448635348761009)
                ·
                  refine ⟨55308495638586476511570757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73744660851448635348761009 55308495638586476511570757)
                  ·
                    refine ⟨10370342932234964345919517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55308495638586476511570757 10370342932234964345919517)
                    ·
                      refine ⟨3888878599588111629719819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10370342932234964345919517 3888878599588111629719819)
                      ·
                        rfl

theorem cell23_7573564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_7573564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573564 prefixEnd_7573564 := by exact prefixLift 7573564
  have htrace : WordTrace (prefixWord ++ tailWord_7573564) baseStart_7573564 baseEnd_7573564 := by
    simpa [prefixWord, tailWord_7573564, baseEnd_7573564] using wordTrace_append hprefix tailTrace_7573564
  have hstable : (prefixWord ++ tailWord_7573564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573564).length < 2 ^ (prefixWord ++ tailWord_7573564).sum := by decide
  have hdescent : baseEnd_7573564 < baseStart_7573564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573618 : List Nat := [3, 2, 1, 2, 2, 2, 4, 2, 5]
def baseStart_7573618 : Nat := 118140960795 + 7573618 * 2 ^ 59
def prefixEnd_7573618 : Nat := 4983230072969 + 3 ^ 40 * 7573618 * 2
def baseEnd_7573618 : Nat := 432100703060383824271619

theorem tailTrace_7573618 : CollatzResearch.WordTrace tailWord_7573618 prefixEnd_7573618 432100703060383824271619 := by
  unfold tailWord_7573618
  simp only [CollatzResearch.WordTrace]
  refine ⟨69058135469020732955256377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184155027917388621214017005 69058135469020732955256377)
  ·
    refine ⟨51793601601765549716442283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69058135469020732955256377 51793601601765549716442283)
    ·
      refine ⟨77690402402648324574663425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51793601601765549716442283 77690402402648324574663425)
      ·
        refine ⟨58267801801986243430997569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77690402402648324574663425 58267801801986243430997569)
        ·
          refine ⟨43700851351489682573248177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58267801801986243430997569 43700851351489682573248177)
          ·
            refine ⟨32775638513617261929936133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43700851351489682573248177 32775638513617261929936133)
            ·
              refine ⟨6145432221303236611863025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32775638513617261929936133 6145432221303236611863025)
              ·
                refine ⟨4609074165977427458897269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145432221303236611863025 4609074165977427458897269)
                ·
                  refine ⟨432100703060383824271619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4609074165977427458897269 432100703060383824271619)
                  ·
                    rfl

theorem cell23_7573618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_7573618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573618 prefixEnd_7573618 := by exact prefixLift 7573618
  have htrace : WordTrace (prefixWord ++ tailWord_7573618) baseStart_7573618 baseEnd_7573618 := by
    simpa [prefixWord, tailWord_7573618, baseEnd_7573618] using wordTrace_append hprefix tailTrace_7573618
  have hstable : (prefixWord ++ tailWord_7573618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573618).length < 2 ^ (prefixWord ++ tailWord_7573618).sum := by decide
  have hdescent : baseEnd_7573618 < baseStart_7573618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573627 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 4, 8]
def baseStart_7573627 : Nat := 118140960795 + 7573627 * 2 ^ 59
def prefixEnd_7573627 : Nat := 4983230072969 + 3 ^ 40 * 7573627 * 2
def baseEnd_7573627 : Nat := 1296303649623114961077343

theorem tailTrace_7573627 : CollatzResearch.WordTrace tailWord_7573627 prefixEnd_7573627 1296303649623114961077343 := by
  unfold tailWord_7573627
  simp only [CollatzResearch.WordTrace]
  refine ⟨276232870133050326358103135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184155246755366884238735423 276232870133050326358103135)
  ·
    refine ⟨414349305199575489537154703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276232870133050326358103135 414349305199575489537154703)
    ·
      refine ⟨621523957799363234305732055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414349305199575489537154703 621523957799363234305732055)
      ·
        refine ⟨932285936699044851458598083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621523957799363234305732055 932285936699044851458598083)
        ·
          refine ⟨1398428905048567277187897125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932285936699044851458598083 1398428905048567277187897125)
          ·
            refine ⟨262205419696606364472730711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1398428905048567277187897125 262205419696606364472730711)
            ·
              refine ⟨393308129544909546709096067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262205419696606364472730711 393308129544909546709096067)
              ·
                refine ⟨589962194317364320063644101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393308129544909546709096067 589962194317364320063644101)
                ·
                  refine ⟨110617911434505810011933269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 589962194317364320063644101 110617911434505810011933269)
                  ·
                    refine ⟨1296303649623114961077343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110617911434505810011933269 1296303649623114961077343)
                    ·
                      rfl

theorem cell23_7573627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 8].length) (baseStart_7573627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573627 prefixEnd_7573627 := by exact prefixLift 7573627
  have htrace : WordTrace (prefixWord ++ tailWord_7573627) baseStart_7573627 baseEnd_7573627 := by
    simpa [prefixWord, tailWord_7573627, baseEnd_7573627] using wordTrace_append hprefix tailTrace_7573627
  have hstable : (prefixWord ++ tailWord_7573627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573627).length < 2 ^ (prefixWord ++ tailWord_7573627).sum := by decide
  have hdescent : baseEnd_7573627 < baseStart_7573627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573664 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_7573664 : Nat := 118140960795 + 7573664 * 2 ^ 59
def prefixEnd_7573664 : Nat := 4983230072969 + 3 ^ 40 * 7573664 * 2
def baseEnd_7573664 : Nat := 3888929947653561238469359

theorem tailTrace_7573664 : CollatzResearch.WordTrace tailWord_7573664 prefixEnd_7573664 3888929947653561238469359 := by
  unfold tailWord_7573664
  simp only [CollatzResearch.WordTrace]
  refine ⟨138117109816958140838600023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184156146422610854451466697 138117109816958140838600023)
  ·
    refine ⟨207175664725437211257900035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138117109816958140838600023 207175664725437211257900035)
    ·
      refine ⟨310763497088155816886850053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207175664725437211257900035 310763497088155816886850053)
      ·
        refine ⟨58268155704029215666284385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310763497088155816886850053 58268155704029215666284385)
        ·
          refine ⟨43701116778021911749713289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58268155704029215666284385 43701116778021911749713289)
          ·
            refine ⟨32775837583516433812284967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43701116778021911749713289 32775837583516433812284967)
            ·
              refine ⟨49163756375274650718427451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32775837583516433812284967 49163756375274650718427451)
              ·
                refine ⟨73745634562911976077641177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49163756375274650718427451 73745634562911976077641177)
                ·
                  refine ⟨55309225922183982058230883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73745634562911976077641177 55309225922183982058230883)
                  ·
                    refine ⟨82963838883275973087346325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55309225922183982058230883 82963838883275973087346325)
                    ·
                      refine ⟨3888929947653561238469359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82963838883275973087346325 3888929947653561238469359)
                      ·
                        rfl

theorem cell23_7573664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_7573664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573664 prefixEnd_7573664 := by exact prefixLift 7573664
  have htrace : WordTrace (prefixWord ++ tailWord_7573664) baseStart_7573664 baseEnd_7573664 := by
    simpa [prefixWord, tailWord_7573664, baseEnd_7573664] using wordTrace_append hprefix tailTrace_7573664
  have hstable : (prefixWord ++ tailWord_7573664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573664).length < 2 ^ (prefixWord ++ tailWord_7573664).sum := by decide
  have hdescent : baseEnd_7573664 < baseStart_7573664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573691 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 6]
def baseStart_7573691 : Nat := 118140960795 + 7573691 * 2 ^ 59
def prefixEnd_7573691 : Nat := 4983230072969 + 3 ^ 40 * 7573691 * 2
def baseEnd_7573691 : Nat := 432104867959025848092415

theorem tailTrace_7573691 : CollatzResearch.WordTrace tailWord_7573691 prefixEnd_7573691 432104867959025848092415 := by
  unfold tailWord_7573691
  simp only [CollatzResearch.WordTrace]
  refine ⟨276235204404818465288432927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184156802936545643525621951 276235204404818465288432927)
  ·
    refine ⟨414352806607227697932649391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276235204404818465288432927 414352806607227697932649391)
    ·
      refine ⟨621529209910841546898974087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414352806607227697932649391 621529209910841546898974087)
      ·
        refine ⟨932293814866262320348461131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621529209910841546898974087 932293814866262320348461131)
        ·
          refine ⟨1398440722299393480522691697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932293814866262320348461131 1398440722299393480522691697)
          ·
            refine ⟨1048830541724545110392018773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398440722299393480522691697 1048830541724545110392018773)
            ·
              refine ⟨6145491455417256506203235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1048830541724545110392018773 6145491455417256506203235)
              ·
                refine ⟨9218237183125884759304853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145491455417256506203235 9218237183125884759304853)
                ·
                  refine ⟨432104867959025848092415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9218237183125884759304853 432104867959025848092415)
                  ·
                    rfl

theorem cell23_7573691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 6].length) (baseStart_7573691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573691 prefixEnd_7573691 := by exact prefixLift 7573691
  have htrace : WordTrace (prefixWord ++ tailWord_7573691) baseStart_7573691 baseEnd_7573691 := by
    simpa [prefixWord, tailWord_7573691, baseEnd_7573691] using wordTrace_append hprefix tailTrace_7573691
  have hstable : (prefixWord ++ tailWord_7573691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573691).length < 2 ^ (prefixWord ++ tailWord_7573691).sum := by decide
  have hdescent : baseEnd_7573691 < baseStart_7573691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573711 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 1, 5, 2]
def baseStart_7573711 : Nat := 118140960795 + 7573711 * 2 ^ 59
def prefixEnd_7573711 : Nat := 4983230072969 + 3 ^ 40 * 7573711 * 2
def baseEnd_7573711 : Nat := 3888954081244322554581643

theorem tailTrace_7573711 : CollatzResearch.WordTrace tailWord_7573711 prefixEnd_7573711 3888954081244322554581643 := by
  unfold tailWord_7573711
  simp only [CollatzResearch.WordTrace]
  refine ⟨276235933864746008704160987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184157289243164005802773991 276235933864746008704160987)
  ·
    refine ⟨414353900797119013056241481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276235933864746008704160987 414353900797119013056241481)
    ·
      refine ⟨310765425597839259792181111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414353900797119013056241481 310765425597839259792181111)
      ·
        refine ⟨466148138396758889688271667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310765425597839259792181111 466148138396758889688271667)
        ·
          refine ⟨699222207595138334532407501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466148138396758889688271667 699222207595138334532407501)
          ·
            refine ⟨262208327848176875449652813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 699222207595138334532407501 262208327848176875449652813)
            ·
              refine ⟨98328122943066328293619805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262208327848176875449652813 98328122943066328293619805)
              ·
                refine ⟨36873046103649873110107427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98328122943066328293619805 36873046103649873110107427)
                ·
                  refine ⟨55309569155474809665161141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36873046103649873110107427 55309569155474809665161141)
                  ·
                    refine ⟨5185272108325763406108857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55309569155474809665161141 5185272108325763406108857)
                    ·
                      refine ⟨3888954081244322554581643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185272108325763406108857 3888954081244322554581643)
                      ·
                        rfl

theorem cell23_7573711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 5, 2].length) (baseStart_7573711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573711 prefixEnd_7573711 := by exact prefixLift 7573711
  have htrace : WordTrace (prefixWord ++ tailWord_7573711) baseStart_7573711 baseEnd_7573711 := by
    simpa [prefixWord, tailWord_7573711, baseEnd_7573711] using wordTrace_append hprefix tailTrace_7573711
  have hstable : (prefixWord ++ tailWord_7573711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573711).length < 2 ^ (prefixWord ++ tailWord_7573711).sum := by decide
  have hdescent : baseEnd_7573711 < baseStart_7573711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573721 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 1, 5]
def baseStart_7573721 : Nat := 118140960795 + 7573721 * 2 ^ 59
def prefixEnd_7573721 : Nat := 4983230072969 + 3 ^ 40 * 7573721 * 2
def baseEnd_7573721 : Nat := 1296319738683622505152199

theorem tailTrace_7573721 : CollatzResearch.WordTrace tailWord_7573721 prefixEnd_7573721 1296319738683622505152199 := by
  unfold tailWord_7573721
  simp only [CollatzResearch.WordTrace]
  refine ⟨276236298594709780412025017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184157532396473186941350011 276236298594709780412025017)
  ·
    refine ⟨207177223946032335309018763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276236298594709780412025017 207177223946032335309018763)
    ·
      refine ⟨310765835919048502963528145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207177223946032335309018763 310765835919048502963528145)
      ·
        refine ⟨233074376939286377222646109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310765835919048502963528145 233074376939286377222646109)
        ·
          refine ⟨87402891352232391458492291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233074376939286377222646109 87402891352232391458492291)
          ·
            refine ⟨131104337028348587187738437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87402891352232391458492291 131104337028348587187738437)
            ·
              refine ⟨24582063192815360097700957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131104337028348587187738437 24582063192815360097700957)
              ·
                refine ⟨9218273697305760036637859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24582063192815360097700957 9218273697305760036637859)
                ·
                  refine ⟨13827410545958640054956789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9218273697305760036637859 13827410545958640054956789)
                  ·
                    refine ⟨1296319738683622505152199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13827410545958640054956789 1296319738683622505152199)
                    ·
                      rfl

theorem cell23_7573721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_7573721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573721 prefixEnd_7573721 := by exact prefixLift 7573721
  have htrace : WordTrace (prefixWord ++ tailWord_7573721) baseStart_7573721 baseEnd_7573721 := by
    simpa [prefixWord, tailWord_7573721, baseEnd_7573721] using wordTrace_append hprefix tailTrace_7573721
  have hstable : (prefixWord ++ tailWord_7573721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573721).length < 2 ^ (prefixWord ++ tailWord_7573721).sum := by decide
  have hdescent : baseEnd_7573721 < baseStart_7573721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573728 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 2, 3, 2]
def baseStart_7573728 : Nat := 118140960795 + 7573728 * 2 ^ 59
def prefixEnd_7573728 : Nat := 4983230072969 + 3 ^ 40 * 7573728 * 2
def baseEnd_7573728 : Nat := 3888962810415448988069065

theorem tailTrace_7573728 : CollatzResearch.WordTrace tailWord_7573728 prefixEnd_7573728 3888962810415448988069065 := by
  unfold tailWord_7573728
  simp only [CollatzResearch.WordTrace]
  refine ⟨138118276952842210303764919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184157702603789613738353225 138118276952842210303764919)
  ·
    refine ⟨207177415429263315455647379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138118276952842210303764919 207177415429263315455647379)
    ·
      refine ⟨310766123143894973183471069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207177415429263315455647379 310766123143894973183471069)
      ·
        refine ⟨116537296178960614943801651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310766123143894973183471069 116537296178960614943801651)
        ·
          refine ⟨174805944268440922415702477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116537296178960614943801651 174805944268440922415702477)
          ·
            refine ⟨65552229100665345905888429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174805944268440922415702477 65552229100665345905888429)
            ·
              refine ⟨24582085912749504714708161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65552229100665345905888429 24582085912749504714708161)
              ·
                refine ⟨18436564434562128536031121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24582085912749504714708161 18436564434562128536031121)
                ·
                  refine ⟨13827423325921596402023341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18436564434562128536031121 13827423325921596402023341)
                  ·
                    refine ⟨5185283747220598650758753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13827423325921596402023341 5185283747220598650758753)
                    ·
                      refine ⟨3888962810415448988069065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185283747220598650758753 3888962810415448988069065)
                      ·
                        rfl

theorem cell23_7573728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_7573728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573728 prefixEnd_7573728 := by exact prefixLift 7573728
  have htrace : WordTrace (prefixWord ++ tailWord_7573728) baseStart_7573728 baseEnd_7573728 := by
    simpa [prefixWord, tailWord_7573728, baseEnd_7573728] using wordTrace_append hprefix tailTrace_7573728
  have hstable : (prefixWord ++ tailWord_7573728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573728).length < 2 ^ (prefixWord ++ tailWord_7573728).sum := by decide
  have hdescent : baseEnd_7573728 < baseStart_7573728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573735 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7573735 : Nat := 118140960795 + 7573735 * 2 ^ 59
def prefixEnd_7573735 : Nat := 4983230072969 + 3 ^ 40 * 7573735 * 2
def baseEnd_7573735 : Nat := 3888966404780030460681533

theorem tailTrace_7573735 : CollatzResearch.WordTrace tailWord_7573735 prefixEnd_7573735 3888966404780030460681533 := by
  unfold tailWord_7573735
  simp only [CollatzResearch.WordTrace]
  refine ⟨276236809216659060803034659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184157872811106040535356439 276236809216659060803034659)
  ·
    refine ⟨414355213824988591204551989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276236809216659060803034659 414355213824988591204551989)
    ·
      refine ⟨38845801296092680425426749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 414355213824988591204551989 38845801296092680425426749)
      ·
        refine ⟨14567175486034755159535031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38845801296092680425426749 14567175486034755159535031)
        ·
          refine ⟨21850763229052132739302547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14567175486034755159535031 21850763229052132739302547)
          ·
            refine ⟨32776144843578199108953821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21850763229052132739302547 32776144843578199108953821)
            ·
              refine ⟨12291054316341824665857683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32776144843578199108953821 12291054316341824665857683)
              ·
                refine ⟨18436581474512736998786525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291054316341824665857683 18436581474512736998786525)
                ·
                  refine ⟨6913718052942276374544947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18436581474512736998786525 6913718052942276374544947)
                  ·
                    refine ⟨10370577079413414561817421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6913718052942276374544947 10370577079413414561817421)
                    ·
                      refine ⟨3888966404780030460681533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10370577079413414561817421 3888966404780030460681533)
                      ·
                        rfl

theorem cell23_7573735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7573735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573735 prefixEnd_7573735 := by exact prefixLift 7573735
  have htrace : WordTrace (prefixWord ++ tailWord_7573735) baseStart_7573735 baseEnd_7573735 := by
    simpa [prefixWord, tailWord_7573735, baseEnd_7573735] using wordTrace_append hprefix tailTrace_7573735
  have hstable : (prefixWord ++ tailWord_7573735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573735).length < 2 ^ (prefixWord ++ tailWord_7573735).sum := by decide
  have hdescent : baseEnd_7573735 < baseStart_7573735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573758 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7573758 : Nat := 118140960795 + 7573758 * 2 ^ 59
def prefixEnd_7573758 : Nat := 4983230072969 + 3 ^ 40 * 7573758 * 2
def baseEnd_7573758 : Nat := 3888978214835083870693927

theorem tailTrace_7573758 : CollatzResearch.WordTrace tailWord_7573758 prefixEnd_7573758 3888978214835083870693927 := by
  unfold tailWord_7573758
  simp only [CollatzResearch.WordTrace]
  refine ⟨34529706011946966966390241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184158432063717157154081285 34529706011946966966390241)
  ·
    refine ⟨25897279508960225224792681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34529706011946966966390241 25897279508960225224792681)
    ·
      refine ⟨19422959631720168918594511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25897279508960225224792681 19422959631720168918594511)
      ·
        refine ⟨29134439447580253377891767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19422959631720168918594511 29134439447580253377891767)
        ·
          refine ⟨43701659171370380066837651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29134439447580253377891767 43701659171370380066837651)
          ·
            refine ⟨65552488757055570100256477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43701659171370380066837651 65552488757055570100256477)
            ·
              refine ⟨24582183283895838787596179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65552488757055570100256477 24582183283895838787596179)
              ·
                refine ⟨36873274925843758181394269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24582183283895838787596179 36873274925843758181394269)
                ·
                  refine ⟨13827478097191409318022851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36873274925843758181394269 13827478097191409318022851)
                  ·
                    refine ⟨20741217145787113977034277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13827478097191409318022851 20741217145787113977034277)
                    ·
                      refine ⟨3888978214835083870693927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20741217145787113977034277 3888978214835083870693927)
                      ·
                        rfl

theorem cell23_7573758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7573758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573758 prefixEnd_7573758 := by exact prefixLift 7573758
  have htrace : WordTrace (prefixWord ++ tailWord_7573758) baseStart_7573758 baseEnd_7573758 := by
    simpa [prefixWord, tailWord_7573758, baseEnd_7573758] using wordTrace_append hprefix tailTrace_7573758
  have hstable : (prefixWord ++ tailWord_7573758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573758).length < 2 ^ (prefixWord ++ tailWord_7573758).sum := by decide
  have hdescent : baseEnd_7573758 < baseStart_7573758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573762 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_7573762 : Nat := 118140960795 + 7573762 * 2 ^ 59
def prefixEnd_7573762 : Nat := 4983230072969 + 3 ^ 40 * 7573762 * 2
def baseEnd_7573762 : Nat := 3888980268757701855043909

theorem tailTrace_7573762 : CollatzResearch.WordTrace tailWord_7573762 prefixEnd_7573762 3888980268757701855043909 := by
  unfold tailWord_7573762
  simp only [CollatzResearch.WordTrace]
  refine ⟨69059448496890311103566885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184158529325040829609511693 69059448496890311103566885)
  ·
    refine ⟨12948646593166933331918791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69059448496890311103566885 12948646593166933331918791)
    ·
      refine ⟨19422969889750399997878187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12948646593166933331918791 19422969889750399997878187)
      ·
        refine ⟨29134454834625599996817281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19422969889750399997878187 29134454834625599996817281)
        ·
          refine ⟨21850841125969199997612961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29134454834625599996817281 21850841125969199997612961)
          ·
            refine ⟨16388130844476899998209721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21850841125969199997612961 16388130844476899998209721)
            ·
              refine ⟨12291098133357674998657291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16388130844476899998209721 12291098133357674998657291)
              ·
                refine ⟨18436647200036512497985937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291098133357674998657291 18436647200036512497985937)
                ·
                  refine ⟨13827485400027384373489453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18436647200036512497985937 13827485400027384373489453)
                  ·
                    refine ⟨5185307025010269140058545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13827485400027384373489453 5185307025010269140058545)
                    ·
                      refine ⟨3888980268757701855043909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185307025010269140058545 3888980268757701855043909)
                      ·
                        rfl

theorem cell23_7573762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_7573762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573762 prefixEnd_7573762 := by exact prefixLift 7573762
  have htrace : WordTrace (prefixWord ++ tailWord_7573762) baseStart_7573762 baseEnd_7573762 := by
    simpa [prefixWord, tailWord_7573762, baseEnd_7573762] using wordTrace_append hprefix tailTrace_7573762
  have hstable : (prefixWord ++ tailWord_7573762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573762).length < 2 ^ (prefixWord ++ tailWord_7573762).sum := by decide
  have hdescent : baseEnd_7573762 < baseStart_7573762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573771 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 4]
def baseStart_7573771 : Nat := 118140960795 + 7573771 * 2 ^ 59
def prefixEnd_7573771 : Nat := 4983230072969 + 3 ^ 40 * 7573771 * 2
def baseEnd_7573771 : Nat := 3888984890083592319831367

theorem tailTrace_7573771 : CollatzResearch.WordTrace tailWord_7573771 prefixEnd_7573771 3888984890083592319831367 := by
  unfold tailWord_7573771
  simp only [CollatzResearch.WordTrace]
  refine ⟨276238122244528638951345167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184158748163019092634230111 276238122244528638951345167)
  ·
    refine ⟨414357183366792958427017751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276238122244528638951345167 414357183366792958427017751)
    ·
      refine ⟨621535775050189437640526627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414357183366792958427017751 621535775050189437640526627)
      ·
        refine ⟨932303662575284156460789941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621535775050189437640526627 932303662575284156460789941)
        ·
          refine ⟨87403468366432889668199057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 932303662575284156460789941 87403468366432889668199057)
          ·
            refine ⟨65552601274824667251149293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87403468366432889668199057 65552601274824667251149293)
            ·
              refine ⟨24582225478059250219180985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65552601274824667251149293 24582225478059250219180985)
              ·
                refine ⟨18436669108544437664385739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24582225478059250219180985 18436669108544437664385739)
                ·
                  refine ⟨27655003662816656496578609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18436669108544437664385739 27655003662816656496578609)
                  ·
                    refine ⟨20741252747112492372433957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27655003662816656496578609 20741252747112492372433957)
                    ·
                      refine ⟨3888984890083592319831367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20741252747112492372433957 3888984890083592319831367)
                      ·
                        rfl

theorem cell23_7573771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 4].length) (baseStart_7573771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573771 prefixEnd_7573771 := by exact prefixLift 7573771
  have htrace : WordTrace (prefixWord ++ tailWord_7573771) baseStart_7573771 baseEnd_7573771 := by
    simpa [prefixWord, tailWord_7573771, baseEnd_7573771] using wordTrace_append hprefix tailTrace_7573771
  have hstable : (prefixWord ++ tailWord_7573771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573771).length < 2 ^ (prefixWord ++ tailWord_7573771).sum := by decide
  have hdescent : baseEnd_7573771 < baseStart_7573771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573786 : List Nat := [3, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3]
def baseStart_7573786 : Nat := 118140960795 + 7573786 * 2 ^ 59
def prefixEnd_7573786 : Nat := 4983230072969 + 3 ^ 40 * 7573786 * 2
def baseEnd_7573786 : Nat := 3888992592293409761143799

theorem tailTrace_7573786 : CollatzResearch.WordTrace tailWord_7573786 prefixEnd_7573786 3888992592293409761143799 := by
  unfold tailWord_7573786
  simp only [CollatzResearch.WordTrace]
  refine ⟨69059667334868574128285303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184159112892982864342094141 69059667334868574128285303)
  ·
    refine ⟨103589501002302861192427955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69059667334868574128285303 103589501002302861192427955)
    ·
      refine ⟨155384251503454291788641933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103589501002302861192427955 155384251503454291788641933)
      ·
        refine ⟨58269094313795359420740725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155384251503454291788641933 58269094313795359420740725)
        ·
          refine ⟨5462727591918314945694443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58269094313795359420740725 5462727591918314945694443)
          ·
            refine ⟨8194091387877472418541665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462727591918314945694443 8194091387877472418541665)
            ·
              refine ⟨6145568540908104313906249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8194091387877472418541665 6145568540908104313906249)
              ·
                refine ⟨4609176405681078235429687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145568540908104313906249 4609176405681078235429687)
                ·
                  refine ⟨6913764608521617353144531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609176405681078235429687 6913764608521617353144531)
                  ·
                    refine ⟨10370646912782426029716797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6913764608521617353144531 10370646912782426029716797)
                    ·
                      refine ⟨3888992592293409761143799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10370646912782426029716797 3888992592293409761143799)
                      ·
                        rfl

theorem cell23_7573786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_7573786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573786 prefixEnd_7573786 := by exact prefixLift 7573786
  have htrace : WordTrace (prefixWord ++ tailWord_7573786) baseStart_7573786 baseEnd_7573786 := by
    simpa [prefixWord, tailWord_7573786, baseEnd_7573786] using wordTrace_append hprefix tailTrace_7573786
  have hstable : (prefixWord ++ tailWord_7573786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573786).length < 2 ^ (prefixWord ++ tailWord_7573786).sum := by decide
  have hdescent : baseEnd_7573786 < baseStart_7573786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573841 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 2, 6]
def baseStart_7573841 : Nat := 118140960795 + 7573841 * 2 ^ 59
def prefixEnd_7573841 : Nat := 4983230072969 + 3 ^ 40 * 7573841 * 2
def baseEnd_7573841 : Nat := 1296340277909802348652015

theorem tailTrace_7573841 : CollatzResearch.WordTrace tailWord_7573841 prefixEnd_7573841 1296340277909802348652015 := by
  unfold tailWord_7573841
  simp only [CollatzResearch.WordTrace]
  refine ⟨276240675354275040906393377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184160450236183360604262251 276240675354275040906393377)
  ·
    refine ⟨207180506515706280679795033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276240675354275040906393377 207180506515706280679795033)
    ·
      refine ⟨155385379886779710509846275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207180506515706280679795033 155385379886779710509846275)
      ·
        refine ⟨233078069830169565764769413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155385379886779710509846275 233078069830169565764769413)
        ·
          refine ⟨43702138093156793580894265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233078069830169565764769413 43702138093156793580894265)
          ·
            refine ⟨32776603569867595185670699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43702138093156793580894265 32776603569867595185670699)
            ·
              refine ⟨49164905354801392778506049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32776603569867595185670699 49164905354801392778506049)
              ·
                refine ⟨36873679016101044583879537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49164905354801392778506049 36873679016101044583879537)
                ·
                  refine ⟨27655259262075783437909653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36873679016101044583879537 27655259262075783437909653)
                  ·
                    refine ⟨1296340277909802348652015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27655259262075783437909653 1296340277909802348652015)
                    ·
                      rfl

theorem cell23_7573841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_7573841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573841 prefixEnd_7573841 := by exact prefixLift 7573841
  have htrace : WordTrace (prefixWord ++ tailWord_7573841) baseStart_7573841 baseEnd_7573841 := by
    simpa [prefixWord, tailWord_7573841, baseEnd_7573841] using wordTrace_append hprefix tailTrace_7573841
  have hstable : (prefixWord ++ tailWord_7573841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573841).length < 2 ^ (prefixWord ++ tailWord_7573841).sum := by decide
  have hdescent : baseEnd_7573841 < baseStart_7573841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573858 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_7573858 : Nat := 118140960795 + 7573858 * 2 ^ 59
def prefixEnd_7573858 : Nat := 4983230072969 + 3 ^ 40 * 7573858 * 2
def baseEnd_7573858 : Nat := 1296343187633511159814489

theorem tailTrace_7573858 : CollatzResearch.WordTrace tailWord_7573858 prefixEnd_7573858 1296343187633511159814489 := by
  unfold tailWord_7573858
  simp only [CollatzResearch.WordTrace]
  refine ⟨69060323848803363202440557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184160863596808968539841485 69060323848803363202440557)
  ·
    refine ⟨25897621443301261200915209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69060323848803363202440557 25897621443301261200915209)
    ·
      refine ⟨19423216082475945900686407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25897621443301261200915209 19423216082475945900686407)
      ·
        refine ⟨29134824123713918851029611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19423216082475945900686407 29134824123713918851029611)
        ·
          refine ⟨43702236185570878276544417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29134824123713918851029611 43702236185570878276544417)
          ·
            refine ⟨32776677139178158707408313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43702236185570878276544417 32776677139178158707408313)
            ·
              refine ⟨24582507854383619030556235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32776677139178158707408313 24582507854383619030556235)
              ·
                refine ⟨36873761781575428545834353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24582507854383619030556235 36873761781575428545834353)
                ·
                  refine ⟨27655321336181571409375765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36873761781575428545834353 27655321336181571409375765)
                  ·
                    refine ⟨1296343187633511159814489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27655321336181571409375765 1296343187633511159814489)
                    ·
                      rfl

theorem cell23_7573858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_7573858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573858 prefixEnd_7573858 := by exact prefixLift 7573858
  have htrace : WordTrace (prefixWord ++ tailWord_7573858) baseStart_7573858 baseEnd_7573858 := by
    simpa [prefixWord, tailWord_7573858, baseEnd_7573858] using wordTrace_append hprefix tailTrace_7573858
  have hstable : (prefixWord ++ tailWord_7573858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573858).length < 2 ^ (prefixWord ++ tailWord_7573858).sum := by decide
  have hdescent : baseEnd_7573858 < baseStart_7573858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573910 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7573910 : Nat := 118140960795 + 7573910 * 2 ^ 59
def prefixEnd_7573910 : Nat := 4983230072969 + 3 ^ 40 * 7573910 * 2
def baseEnd_7573910 : Nat := 3889056263894567275993229

theorem tailTrace_7573910 : CollatzResearch.WordTrace tailWord_7573910 prefixEnd_7573910 3889056263894567275993229 := by
  unfold tailWord_7573910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265199499439066605665949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184162127994016710460436789 17265199499439066605665949)
  ·
    refine ⟨6474449812289649977124731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17265199499439066605665949 6474449812289649977124731)
    ·
      refine ⟨9711674718434474965687097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6474449812289649977124731 9711674718434474965687097)
      ·
        refine ⟨7283756038825856224265323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9711674718434474965687097 7283756038825856224265323)
        ·
          refine ⟨10925634058238784336397985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7283756038825856224265323 10925634058238784336397985)
          ·
            refine ⟨8194225543679088252298489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10925634058238784336397985 8194225543679088252298489)
            ·
              refine ⟨6145669157759316189223867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8194225543679088252298489 6145669157759316189223867)
              ·
                refine ⟨9218503736638974283835801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145669157759316189223867 9218503736638974283835801)
                ·
                  refine ⟨6913877802479230712876851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9218503736638974283835801 6913877802479230712876851)
                  ·
                    refine ⟨10370816703718846069315277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6913877802479230712876851 10370816703718846069315277)
                    ·
                      refine ⟨3889056263894567275993229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10370816703718846069315277 3889056263894567275993229)
                      ·
                        rfl

theorem cell23_7573910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7573910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573910 prefixEnd_7573910 := by exact prefixLift 7573910
  have htrace : WordTrace (prefixWord ++ tailWord_7573910) baseStart_7573910 baseEnd_7573910 := by
    simpa [prefixWord, tailWord_7573910, baseEnd_7573910] using wordTrace_append hprefix tailTrace_7573910
  have hstable : (prefixWord ++ tailWord_7573910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573910).length < 2 ^ (prefixWord ++ tailWord_7573910).sum := by decide
  have hdescent : baseEnd_7573910 < baseStart_7573910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573911 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_7573911 : Nat := 118140960795 + 7573911 * 2 ^ 59
def prefixEnd_7573911 : Nat := 4983230072969 + 3 ^ 40 * 7573911 * 2
def baseEnd_7573911 : Nat := 3889056777375221772080723

theorem tailTrace_7573911 : CollatzResearch.WordTrace tailWord_7573911 prefixEnd_7573911 3889056777375221772080723 := by
  unfold tailWord_7573911
  simp only [CollatzResearch.WordTrace]
  refine ⟨276243228464021442861441587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184162152309347628574294391 276243228464021442861441587)
  ·
    refine ⟨414364842696032164292162381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276243228464021442861441587 414364842696032164292162381)
    ·
      refine ⟨155386816011012061609560893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414364842696032164292162381 155386816011012061609560893)
      ·
        refine ⟨58270056004129523103585335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155386816011012061609560893 58270056004129523103585335)
        ·
          refine ⟨87405084006194284655378003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58270056004129523103585335 87405084006194284655378003)
          ·
            refine ⟨131107626009291426983067005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87405084006194284655378003 131107626009291426983067005)
            ·
              refine ⟨49165359753484285118650127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131107626009291426983067005 49165359753484285118650127)
              ·
                refine ⟨73748039630226427677975191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49165359753484285118650127 73748039630226427677975191)
                ·
                  refine ⟨110622059445339641516962787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73748039630226427677975191 110622059445339641516962787)
                  ·
                    refine ⟨165933089168009462275444181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110622059445339641516962787 165933089168009462275444181)
                    ·
                      refine ⟨3889056777375221772080723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165933089168009462275444181 3889056777375221772080723)
                      ·
                        rfl

theorem cell23_7573911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_7573911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573911 prefixEnd_7573911 := by exact prefixLift 7573911
  have htrace : WordTrace (prefixWord ++ tailWord_7573911) baseStart_7573911 baseEnd_7573911 := by
    simpa [prefixWord, tailWord_7573911, baseEnd_7573911] using wordTrace_append hprefix tailTrace_7573911
  have hstable : (prefixWord ++ tailWord_7573911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573911).length < 2 ^ (prefixWord ++ tailWord_7573911).sum := by decide
  have hdescent : baseEnd_7573911 < baseStart_7573911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573956 : List Nat := [2, 3, 3, 2, 3, 1, 2, 2, 5]
def baseStart_7573956 : Nat := 118140960795 + 7573956 * 2 ^ 59
def prefixEnd_7573956 : Nat := 4983230072969 + 3 ^ 40 * 7573956 * 2
def baseEnd_7573956 : Nat := 432119987111630455113113

theorem tailTrace_7573956 : CollatzResearch.WordTrace tailWord_7573956 prefixEnd_7573956 432119987111630455113113 := by
  unfold tailWord_7573956
  simp only [CollatzResearch.WordTrace]
  refine ⟨138122434874429207773414861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184163246499238943697886481 138122434874429207773414861)
  ·
    refine ⟨51795913077910952915030573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138122434874429207773414861 51795913077910952915030573)
    ·
      refine ⟨19423467404216607343136465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51795913077910952915030573 19423467404216607343136465)
      ·
        refine ⟨14567600553162455507352349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19423467404216607343136465 14567600553162455507352349)
        ·
          refine ⟨5462850207435920815257131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14567600553162455507352349 5462850207435920815257131)
          ·
            refine ⟨8194275311153881222885697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462850207435920815257131 8194275311153881222885697)
            ·
              refine ⟨6145706483365410917164273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8194275311153881222885697 6145706483365410917164273)
              ·
                refine ⟨4609279862524058187873205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145706483365410917164273 4609279862524058187873205)
                ·
                  refine ⟨432119987111630455113113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4609279862524058187873205 432119987111630455113113)
                  ·
                    rfl

theorem cell23_7573956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_7573956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573956 prefixEnd_7573956 := by exact prefixLift 7573956
  have htrace : WordTrace (prefixWord ++ tailWord_7573956) baseStart_7573956 baseEnd_7573956 := by
    simpa [prefixWord, tailWord_7573956, baseEnd_7573956] using wordTrace_append hprefix tailTrace_7573956
  have hstable : (prefixWord ++ tailWord_7573956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573956).length < 2 ^ (prefixWord ++ tailWord_7573956).sum := by decide
  have hdescent : baseEnd_7573956 < baseStart_7573956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573961 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 8]
def baseStart_7573961 : Nat := 118140960795 + 7573961 * 2 ^ 59
def prefixEnd_7573961 : Nat := 4983230072969 + 3 ^ 40 * 7573961 * 2
def baseEnd_7573961 : Nat := 432120272378660730717277

theorem tailTrace_7573961 : CollatzResearch.WordTrace tailWord_7573961 prefixEnd_7573961 432120272378660730717277 := by
  unfold tailWord_7573961
  simp only [CollatzResearch.WordTrace]
  refine ⟨276245052113840301400761737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184163368075893534267174491 276245052113840301400761737)
  ·
    refine ⟨207183789085380226050571303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276245052113840301400761737 207183789085380226050571303)
    ·
      refine ⟨310775683628070339075856955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207183789085380226050571303 310775683628070339075856955)
      ·
        refine ⟨466163525442105508613785433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310775683628070339075856955 466163525442105508613785433)
        ·
          refine ⟨349622644081579131460339075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466163525442105508613785433 349622644081579131460339075)
          ·
            refine ⟨524433966122368697190508613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349622644081579131460339075 524433966122368697190508613)
            ·
              refine ⟨98331368647944130723220365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 524433966122368697190508613 98331368647944130723220365)
              ·
                refine ⟨36874263242979049021207637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98331368647944130723220365 36874263242979049021207637)
                ·
                  refine ⟨432120272378660730717277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36874263242979049021207637 432120272378660730717277)
                  ·
                    rfl

theorem cell23_7573961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 8].length) (baseStart_7573961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573961 prefixEnd_7573961 := by exact prefixLift 7573961
  have htrace : WordTrace (prefixWord ++ tailWord_7573961) baseStart_7573961 baseEnd_7573961 := by
    simpa [prefixWord, tailWord_7573961, baseEnd_7573961] using wordTrace_append hprefix tailTrace_7573961
  have hstable : (prefixWord ++ tailWord_7573961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573961).length < 2 ^ (prefixWord ++ tailWord_7573961).sum := by decide
  have hdescent : baseEnd_7573961 < baseStart_7573961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573972 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_7573972 : Nat := 118140960795 + 7573972 * 2 ^ 59
def prefixEnd_7573972 : Nat := 4983230072969 + 3 ^ 40 * 7573972 * 2
def baseEnd_7573972 : Nat := 3889088099695146033417943

theorem tailTrace_7573972 : CollatzResearch.WordTrace tailWord_7573972 prefixEnd_7573972 3889088099695146033417943 := by
  unfold tailWord_7573972
  simp only [CollatzResearch.WordTrace]
  refine ⟨138122726658400225139706085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184163635544533633519608113 138122726658400225139706085)
  ·
    refine ⟨25898011248450042213694891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138122726658400225139706085 25898011248450042213694891)
    ·
      refine ⟨38847016872675063320542337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25898011248450042213694891 38847016872675063320542337)
      ·
        refine ⟨29135262654506297490406753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38847016872675063320542337 29135262654506297490406753)
        ·
          refine ⟨21851446990879723117805065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29135262654506297490406753 21851446990879723117805065)
          ·
            refine ⟨16388585243159792338353799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21851446990879723117805065 16388585243159792338353799)
            ·
              refine ⟨24582877864739688507530699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16388585243159792338353799 24582877864739688507530699)
              ·
                refine ⟨36874316797109532761296049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24582877864739688507530699 36874316797109532761296049)
                ·
                  refine ⟨27655737597832149570972037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36874316797109532761296049 27655737597832149570972037)
                  ·
                    refine ⟨5185450799593528044557257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27655737597832149570972037 5185450799593528044557257)
                    ·
                      refine ⟨3889088099695146033417943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185450799593528044557257 3889088099695146033417943)
                      ·
                        rfl

theorem cell23_7573972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_7573972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573972 prefixEnd_7573972 := by exact prefixLift 7573972
  have htrace : WordTrace (prefixWord ++ tailWord_7573972) baseStart_7573972 baseEnd_7573972 := by
    simpa [prefixWord, tailWord_7573972, baseEnd_7573972] using wordTrace_append hprefix tailTrace_7573972
  have hstable : (prefixWord ++ tailWord_7573972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573972).length < 2 ^ (prefixWord ++ tailWord_7573972).sum := by decide
  have hdescent : baseEnd_7573972 < baseStart_7573972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573978 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 6]
def baseStart_7573978 : Nat := 118140960795 + 7573978 * 2 ^ 59
def prefixEnd_7573978 : Nat := 4983230072969 + 3 ^ 40 * 7573978 * 2
def baseEnd_7573978 : Nat := 432121242286563667771435

theorem tailTrace_7573978 : CollatzResearch.WordTrace tailWord_7573978 prefixEnd_7573978 432121242286563667771435 := by
  unfold tailWord_7573978
  simp only [CollatzResearch.WordTrace]
  refine ⟨69061418038694678326032647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184163781436519142202753725 69061418038694678326032647)
  ·
    refine ⟨103592127058042017489048971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69061418038694678326032647 103592127058042017489048971)
    ·
      refine ⟨155388190587063026233573457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103592127058042017489048971 155388190587063026233573457)
      ·
        refine ⟨116541142940297269675180093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155388190587063026233573457 116541142940297269675180093)
        ·
          refine ⟨43702928602611476128192535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116541142940297269675180093 43702928602611476128192535)
          ·
            refine ⟨65554392903917214192288803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43702928602611476128192535 65554392903917214192288803)
            ·
              refine ⟨98331589355875821288433205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65554392903917214192288803 98331589355875821288433205)
              ·
                refine ⟨9218586502113358245790613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98331589355875821288433205 9218586502113358245790613)
                ·
                  refine ⟨432121242286563667771435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9218586502113358245790613 432121242286563667771435)
                  ·
                    rfl

theorem cell23_7573978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_7573978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573978 prefixEnd_7573978 := by exact prefixLift 7573978
  have htrace : WordTrace (prefixWord ++ tailWord_7573978) baseStart_7573978 baseEnd_7573978 := by
    simpa [prefixWord, tailWord_7573978, baseEnd_7573978] using wordTrace_append hprefix tailTrace_7573978
  have hstable : (prefixWord ++ tailWord_7573978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573978).length < 2 ^ (prefixWord ++ tailWord_7573978).sum := by decide
  have hdescent : baseEnd_7573978 < baseStart_7573978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573986 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7573986 : Nat := 118140960795 + 7573986 * 2 ^ 59
def prefixEnd_7573986 : Nat := 4983230072969 + 3 ^ 40 * 7573986 * 2
def baseEnd_7573986 : Nat := 1296365096141436326214293

theorem tailTrace_7573986 : CollatzResearch.WordTrace tailWord_7573986 prefixEnd_7573986 1296365096141436326214293 := by
  unfold tailWord_7573986
  simp only [CollatzResearch.WordTrace]
  refine ⟨69061490984687432667605453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184163975959166487113614541 69061490984687432667605453)
  ·
    refine ⟨25898059119257787250352045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69061490984687432667605453 25898059119257787250352045)
    ·
      refine ⟨9711772169721670218882017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25898059119257787250352045 9711772169721670218882017)
      ·
        refine ⟨7283829127291252664161513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9711772169721670218882017 7283829127291252664161513)
        ·
          refine ⟨5462871845468439498121135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7283829127291252664161513 5462871845468439498121135)
          ·
            refine ⟨8194307768202659247181703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462871845468439498121135 8194307768202659247181703)
            ·
              refine ⟨12291461652303988870772555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194307768202659247181703 12291461652303988870772555)
              ·
                refine ⟨18437192478455983306158833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291461652303988870772555 18437192478455983306158833)
                ·
                  refine ⟨13827894358841987479619125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18437192478455983306158833 13827894358841987479619125)
                  ·
                    refine ⟨1296365096141436326214293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13827894358841987479619125 1296365096141436326214293)
                    ·
                      rfl

theorem cell23_7573986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7573986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573986 prefixEnd_7573986 := by exact prefixLift 7573986
  have htrace : WordTrace (prefixWord ++ tailWord_7573986) baseStart_7573986 baseEnd_7573986 := by
    simpa [prefixWord, tailWord_7573986, baseEnd_7573986] using wordTrace_append hprefix tailTrace_7573986
  have hstable : (prefixWord ++ tailWord_7573986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573986).length < 2 ^ (prefixWord ++ tailWord_7573986).sum := by decide
  have hdescent : baseEnd_7573986 < baseStart_7573986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573989 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7573989 : Nat := 118140960795 + 7573989 * 2 ^ 59
def prefixEnd_7573989 : Nat := 4983230072969 + 3 ^ 40 * 7573989 * 2
def baseEnd_7573989 : Nat := 3889096828866272466905365

theorem tailTrace_7573989 : CollatzResearch.WordTrace tailWord_7573989 prefixEnd_7573989 3889096828866272466905365 := by
  unfold tailWord_7573989
  simp only [CollatzResearch.WordTrace]
  refine ⟨276246073357738862182781021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184164048905159241455187347 276246073357738862182781021)
  ·
    refine ⟨103592277509152073318542883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276246073357738862182781021 103592277509152073318542883)
    ·
      refine ⟨155388416263728109977814325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103592277509152073318542883 155388416263728109977814325)
      ·
        refine ⟨14567664024724510310420093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155388416263728109977814325 14567664024724510310420093)
        ·
          refine ⟨5462874009271691366407535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14567664024724510310420093 5462874009271691366407535)
          ·
            refine ⟨8194311013907537049611303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462874009271691366407535 8194311013907537049611303)
            ·
              refine ⟨12291466520861305574416955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194311013907537049611303 12291466520861305574416955)
              ·
                refine ⟨18437199781291958361625433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291466520861305574416955 18437199781291958361625433)
                ·
                  refine ⟨13827899835968968771219075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18437199781291958361625433 13827899835968968771219075)
                  ·
                    refine ⟨20741849753953453156828613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13827899835968968771219075 20741849753953453156828613)
                    ·
                      refine ⟨3889096828866272466905365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20741849753953453156828613 3889096828866272466905365)
                      ·
                        rfl

theorem cell23_7573989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7573989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573989 prefixEnd_7573989 := by exact prefixLift 7573989
  have htrace : WordTrace (prefixWord ++ tailWord_7573989) baseStart_7573989 baseEnd_7573989 := by
    simpa [prefixWord, tailWord_7573989, baseEnd_7573989] using wordTrace_append hprefix tailTrace_7573989
  have hstable : (prefixWord ++ tailWord_7573989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573989).length < 2 ^ (prefixWord ++ tailWord_7573989).sum := by decide
  have hdescent : baseEnd_7573989 < baseStart_7573989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7573992 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_7573992 : Nat := 118140960795 + 7573992 * 2 ^ 59
def prefixEnd_7573992 : Nat := 4983230072969 + 3 ^ 40 * 7573992 * 2
def baseEnd_7573992 : Nat := 3889098369308235955167851

theorem tailTrace_7573992 : CollatzResearch.WordTrace tailWord_7573992 prefixEnd_7573992 3889098369308235955167851 := by
  unfold tailWord_7573992
  simp only [CollatzResearch.WordTrace]
  refine ⟨138123091388363996847570115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184164121851151995796760153 138123091388363996847570115)
  ·
    refine ⟨207184637082545995271355173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138123091388363996847570115 207184637082545995271355173)
    ·
      refine ⟨38847119452977374113379095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207184637082545995271355173 38847119452977374113379095)
      ·
        refine ⟨58270679179466061170068643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38847119452977374113379095 58270679179466061170068643)
        ·
          refine ⟨87406018769199091755102965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58270679179466061170068643 87406018769199091755102965)
          ·
            refine ⟨8194314259612414852040903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87406018769199091755102965 8194314259612414852040903)
            ·
              refine ⟨12291471389418622278061355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194314259612414852040903 12291471389418622278061355)
              ·
                refine ⟨18437207084127933417092033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12291471389418622278061355 18437207084127933417092033)
                ·
                  refine ⟨13827905313095950062819025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18437207084127933417092033 13827905313095950062819025)
                  ·
                    refine ⟨10370928984821962547114269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13827905313095950062819025 10370928984821962547114269)
                    ·
                      refine ⟨3889098369308235955167851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10370928984821962547114269 3889098369308235955167851)
                      ·
                        rfl

theorem cell23_7573992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_7573992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7573992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7573992 prefixEnd_7573992 := by exact prefixLift 7573992
  have htrace : WordTrace (prefixWord ++ tailWord_7573992) baseStart_7573992 baseEnd_7573992 := by
    simpa [prefixWord, tailWord_7573992, baseEnd_7573992] using wordTrace_append hprefix tailTrace_7573992
  have hstable : (prefixWord ++ tailWord_7573992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7573992).length < 2 ^ (prefixWord ++ tailWord_7573992).sum := by decide
  have hdescent : baseEnd_7573992 < baseStart_7573992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7573992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574015 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 4, 3, 2]
def baseStart_7574015 : Nat := 118140960795 + 7574015 * 2 ^ 59
def prefixEnd_7574015 : Nat := 4983230072969 + 3 ^ 40 * 7574015 * 2
def baseEnd_7574015 : Nat := 3889110179363289365180245

theorem tailTrace_7574015 : CollatzResearch.WordTrace tailWord_7574015 prefixEnd_7574015 3889110179363289365180245 := by
  unfold tailWord_7574015
  simp only [CollatzResearch.WordTrace]
  refine ⟨276247021655644668623227499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184164681103763112415484999 276247021655644668623227499)
  ·
    refine ⟨414370532483467002934841249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276247021655644668623227499 414370532483467002934841249)
    ·
      refine ⟨310777899362600252201130937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414370532483467002934841249 310777899362600252201130937)
      ·
        refine ⟨233083424521950189150848203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310777899362600252201130937 233083424521950189150848203)
        ·
          refine ⟨349625136782925283726272305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233083424521950189150848203 349625136782925283726272305)
          ·
            refine ⟨262218852587193962794704229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349625136782925283726272305 262218852587193962794704229)
            ·
              refine ⟨49166034860098868024007043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262218852587193962794704229 49166034860098868024007043)
              ·
                refine ⟨73749052290148302036010565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49166034860098868024007043 73749052290148302036010565)
                ·
                  refine ⟨13827947304402806631751981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73749052290148302036010565 13827947304402806631751981)
                  ·
                    refine ⟨5185480239151052486906993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13827947304402806631751981 5185480239151052486906993)
                    ·
                      refine ⟨3889110179363289365180245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185480239151052486906993 3889110179363289365180245)
                      ·
                        rfl

theorem cell23_7574015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_7574015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574015 prefixEnd_7574015 := by exact prefixLift 7574015
  have htrace : WordTrace (prefixWord ++ tailWord_7574015) baseStart_7574015 baseEnd_7574015 := by
    simpa [prefixWord, tailWord_7574015, baseEnd_7574015] using wordTrace_append hprefix tailTrace_7574015
  have hstable : (prefixWord ++ tailWord_7574015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574015).length < 2 ^ (prefixWord ++ tailWord_7574015).sum := by decide
  have hdescent : baseEnd_7574015 < baseStart_7574015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574056 : List Nat := [2, 1, 5, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7574056 : Nat := 118140960795 + 7574056 * 2 ^ 59
def prefixEnd_7574056 : Nat := 4983230072969 + 3 ^ 40 * 7574056 * 2
def baseEnd_7574056 : Nat := 3889131232070123704767557

theorem tailTrace_7574056 : CollatzResearch.WordTrace tailWord_7574056 prefixEnd_7574056 3889131232070123704767557 := by
  unfold tailWord_7574056
  simp only [CollatzResearch.WordTrace]
  refine ⟨138124258524248066312735011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184165678032330755083646681 138124258524248066312735011)
  ·
    refine ⟨207186387786372099469102517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138124258524248066312735011 207186387786372099469102517)
    ·
      refine ⟨19423723854972384325228361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207186387786372099469102517 19423723854972384325228361)
      ·
        refine ⟨14567792891229288243921271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19423723854972384325228361 14567792891229288243921271)
        ·
          refine ⟨21851689336843932365881907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14567792891229288243921271 21851689336843932365881907)
          ·
            refine ⟨32777534005265898548822861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21851689336843932365881907 32777534005265898548822861)
            ·
              refine ⟨12291575251974711955808573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32777534005265898548822861 12291575251974711955808573)
              ·
                refine ⟨4609340719490516983428215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12291575251974711955808573 4609340719490516983428215)
                ·
                  refine ⟨6914011079235775475142323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609340719490516983428215 6914011079235775475142323)
                  ·
                    refine ⟨10371016618853663212713485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6914011079235775475142323 10371016618853663212713485)
                    ·
                      refine ⟨3889131232070123704767557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371016618853663212713485 3889131232070123704767557)
                      ·
                        rfl

theorem cell23_7574056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7574056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574056 prefixEnd_7574056 := by exact prefixLift 7574056
  have htrace : WordTrace (prefixWord ++ tailWord_7574056) baseStart_7574056 baseEnd_7574056 := by
    simpa [prefixWord, tailWord_7574056, baseEnd_7574056] using wordTrace_append hprefix tailTrace_7574056
  have hstable : (prefixWord ++ tailWord_7574056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574056).length < 2 ^ (prefixWord ++ tailWord_7574056).sum := by decide
  have hdescent : baseEnd_7574056 < baseStart_7574056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574130 : List Nat := [3, 2, 1, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_7574130 : Nat := 118140960795 + 7574130 * 2 ^ 59
def prefixEnd_7574130 : Nat := 4983230072969 + 3 ^ 40 * 7574130 * 2
def baseEnd_7574130 : Nat := 3889169229638556415242217

theorem tailTrace_7574130 : CollatzResearch.WordTrace tailWord_7574130 prefixEnd_7574130 3889169229638556415242217 := by
  unfold tailWord_7574130
  simp only [CollatzResearch.WordTrace]
  refine ⟨69062804012557010815915961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184167477366818695509109229 69062804012557010815915961)
  ·
    refine ⟨51797103009417758111936971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69062804012557010815915961 51797103009417758111936971)
    ·
      refine ⟨77695654514126637167905457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51797103009417758111936971 77695654514126637167905457)
      ·
        refine ⟨58271740885594977875929093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77695654514126637167905457 58271740885594977875929093)
        ·
          refine ⟨10925951416049058351736705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58271740885594977875929093 10925951416049058351736705)
          ·
            refine ⟨8194463562036793763802529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10925951416049058351736705 8194463562036793763802529)
            ·
              refine ⟨6145847671527595322851897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8194463562036793763802529 6145847671527595322851897)
              ·
                refine ⟨4609385753645696492138923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145847671527595322851897 4609385753645696492138923)
                ·
                  refine ⟨6914078630468544738208385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609385753645696492138923 6914078630468544738208385)
                  ·
                    refine ⟨5185558972851408553656289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6914078630468544738208385 5185558972851408553656289)
                    ·
                      refine ⟨3889169229638556415242217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185558972851408553656289 3889169229638556415242217)
                      ·
                        rfl

theorem cell23_7574130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_7574130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574130 prefixEnd_7574130 := by exact prefixLift 7574130
  have htrace : WordTrace (prefixWord ++ tailWord_7574130) baseStart_7574130 baseEnd_7574130 := by
    simpa [prefixWord, tailWord_7574130, baseEnd_7574130] using wordTrace_append hprefix tailTrace_7574130
  have hstable : (prefixWord ++ tailWord_7574130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574130).length < 2 ^ (prefixWord ++ tailWord_7574130).sum := by decide
  have hdescent : baseEnd_7574130 < baseStart_7574130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574145 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 2, 6]
def baseStart_7574145 : Nat := 118140960795 + 7574145 * 2 ^ 59
def prefixEnd_7574145 : Nat := 4983230072969 + 3 ^ 40 * 7574145 * 2
def baseEnd_7574145 : Nat := 1296392310616124618851549

theorem tailTrace_7574145 : CollatzResearch.WordTrace tailWord_7574145 prefixEnd_7574145 1296392310616124618851549 := by
  unfold tailWord_7574145
  simp only [CollatzResearch.WordTrace]
  refine ⟨276251763145173700825459889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184167842096782467216973259 276251763145173700825459889)
  ·
    refine ⟨207188822358880275619094917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276251763145173700825459889 207188822358880275619094917)
    ·
      refine ⟨38847904192290051678580297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207188822358880275619094917 38847904192290051678580297)
      ·
        refine ⟨29135928144217538758935223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38847904192290051678580297 29135928144217538758935223)
        ·
          refine ⟨43703892216326308138402835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29135928144217538758935223 43703892216326308138402835)
          ·
            refine ⟨65555838324489462207604253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43703892216326308138402835 65555838324489462207604253)
            ·
              refine ⟨24583439371683548327851595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65555838324489462207604253 24583439371683548327851595)
              ·
                refine ⟨36875159057525322491777393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24583439371683548327851595 36875159057525322491777393)
                ·
                  refine ⟨27656369293143991868833045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36875159057525322491777393 27656369293143991868833045)
                  ·
                    refine ⟨1296392310616124618851549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27656369293143991868833045 1296392310616124618851549)
                    ·
                      rfl

theorem cell23_7574145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_7574145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574145 prefixEnd_7574145 := by exact prefixLift 7574145
  have htrace : WordTrace (prefixWord ++ tailWord_7574145) baseStart_7574145 baseEnd_7574145 := by
    simpa [prefixWord, tailWord_7574145, baseEnd_7574145] using wordTrace_append hprefix tailTrace_7574145
  have hstable : (prefixWord ++ tailWord_7574145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574145).length < 2 ^ (prefixWord ++ tailWord_7574145).sum := by decide
  have hdescent : baseEnd_7574145 < baseStart_7574145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574185 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 3]
def baseStart_7574185 : Nat := 118140960795 + 7574185 * 2 ^ 59
def prefixEnd_7574185 : Nat := 4983230072969 + 3 ^ 40 * 7574185 * 2
def baseEnd_7574185 : Nat := 3889197471074553700054463

theorem tailTrace_7574185 : CollatzResearch.WordTrace tailWord_7574185 prefixEnd_7574185 3889197471074553700054463 := by
  unfold tailWord_7574185
  simp only [CollatzResearch.WordTrace]
  refine ⟨276253222065028787656916009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184168814710019191771277339 276253222065028787656916009)
  ·
    refine ⟨207189916548771590742687007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276253222065028787656916009 207189916548771590742687007)
    ·
      refine ⟨310784874823157386114030511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207189916548771590742687007 310784874823157386114030511)
      ·
        refine ⟨466177312234736079171045767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310784874823157386114030511 466177312234736079171045767)
        ·
          refine ⟨699265968352104118756568651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466177312234736079171045767 699265968352104118756568651)
          ·
            refine ⟨1048898952528156178134852977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699265968352104118756568651 1048898952528156178134852977)
            ·
              refine ⟨786674214396117133601139733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048898952528156178134852977 786674214396117133601139733)
              ·
                refine ⟨36875353799817990637553425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 786674214396117133601139733 36875353799817990637553425)
                ·
                  refine ⟨27656515349863492978165069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36875353799817990637553425 27656515349863492978165069)
                  ·
                    refine ⟨10371193256198809866811901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27656515349863492978165069 10371193256198809866811901)
                    ·
                      refine ⟨3889197471074553700054463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371193256198809866811901 3889197471074553700054463)
                      ·
                        rfl

theorem cell23_7574185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_7574185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574185 prefixEnd_7574185 := by exact prefixLift 7574185
  have htrace : WordTrace (prefixWord ++ tailWord_7574185) baseStart_7574185 baseEnd_7574185 := by
    simpa [prefixWord, tailWord_7574185, baseEnd_7574185] using wordTrace_append hprefix tailTrace_7574185
  have hstable : (prefixWord ++ tailWord_7574185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574185).length < 2 ^ (prefixWord ++ tailWord_7574185).sum := by decide
  have hdescent : baseEnd_7574185 < baseStart_7574185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574205 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_7574205 : Nat := 118140960795 + 7574205 * 2 ^ 59
def prefixEnd_7574205 : Nat := 4983230072969 + 3 ^ 40 * 7574205 * 2
def baseEnd_7574205 : Nat := 1296402580229214540601457

theorem tailTrace_7574205 : CollatzResearch.WordTrace tailWord_7574205 prefixEnd_7574205 1296402580229214540601457 := by
  unfold tailWord_7574205
  simp only [CollatzResearch.WordTrace]
  refine ⟨276253951524956331072644069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184169301016637554048429379 276253951524956331072644069)
  ·
    refine ⟨51797615910929312076120763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276253951524956331072644069 51797615910929312076120763)
    ·
      refine ⟨77696423866393968114181145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51797615910929312076120763 77696423866393968114181145)
      ·
        refine ⟨58272317899795476085635859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77696423866393968114181145 58272317899795476085635859)
        ·
          refine ⟨87408476849693214128453789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58272317899795476085635859 87408476849693214128453789)
          ·
            refine ⟨32778178818634955298170171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87408476849693214128453789 32778178818634955298170171)
            ·
              refine ⟨49167268227952432947255257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32778178818634955298170171 49167268227952432947255257)
              ·
                refine ⟨36875451170964324710441443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49167268227952432947255257 36875451170964324710441443)
                ·
                  refine ⟨55313176756446487065662165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36875451170964324710441443 55313176756446487065662165)
                  ·
                    refine ⟨1296402580229214540601457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55313176756446487065662165 1296402580229214540601457)
                    ·
                      rfl

theorem cell23_7574205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_7574205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574205 prefixEnd_7574205 := by exact prefixLift 7574205
  have htrace : WordTrace (prefixWord ++ tailWord_7574205) baseStart_7574205 baseEnd_7574205 := by
    simpa [prefixWord, tailWord_7574205, baseEnd_7574205] using wordTrace_append hprefix tailTrace_7574205
  have hstable : (prefixWord ++ tailWord_7574205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574205).length < 2 ^ (prefixWord ++ tailWord_7574205).sum := by decide
  have hdescent : baseEnd_7574205 < baseStart_7574205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574225 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_7574225 : Nat := 118140960795 + 7574225 * 2 ^ 59
def prefixEnd_7574225 : Nat := 4983230072969 + 3 ^ 40 * 7574225 * 2
def baseEnd_7574225 : Nat := 3889218010300733543554279

theorem tailTrace_7574225 : CollatzResearch.WordTrace tailWord_7574225 prefixEnd_7574225 3889218010300733543554279 := by
  unfold tailWord_7574225
  simp only [CollatzResearch.WordTrace]
  refine ⟨276254680984883874488372129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184169787323255916325581419 276254680984883874488372129)
  ·
    refine ⟨207191010738662905866279097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276254680984883874488372129 207191010738662905866279097)
    ·
      refine ⟨155393258053997179399709323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207191010738662905866279097 155393258053997179399709323)
      ·
        refine ⟨233089887080995769099563985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155393258053997179399709323 233089887080995769099563985)
        ·
          refine ⟨174817415310746826824672989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233089887080995769099563985 174817415310746826824672989)
          ·
            refine ⟨65556530741530060059252371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174817415310746826824672989 65556530741530060059252371)
            ·
              refine ⟨98334796112295090088878557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65556530741530060059252371 98334796112295090088878557)
              ·
                refine ⟨36875548542110658783329459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98334796112295090088878557 36875548542110658783329459)
                ·
                  refine ⟨55313322813165988174994189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36875548542110658783329459 55313322813165988174994189)
                  ·
                    refine ⟨20742496054937245565622821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55313322813165988174994189 20742496054937245565622821)
                    ·
                      refine ⟨3889218010300733543554279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20742496054937245565622821 3889218010300733543554279)
                      ·
                        rfl

theorem cell23_7574225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_7574225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574225 prefixEnd_7574225 := by exact prefixLift 7574225
  have htrace : WordTrace (prefixWord ++ tailWord_7574225) baseStart_7574225 baseEnd_7574225 := by
    simpa [prefixWord, tailWord_7574225, baseEnd_7574225] using wordTrace_append hprefix tailTrace_7574225
  have hstable : (prefixWord ++ tailWord_7574225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574225).length < 2 ^ (prefixWord ++ tailWord_7574225).sum := by decide
  have hdescent : baseEnd_7574225 < baseStart_7574225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574226 : List Nat := [3, 2, 2, 2, 3, 2, 1, 3, 5]
def baseStart_7574226 : Nat := 118140960795 + 7574226 * 2 ^ 59
def prefixEnd_7574226 : Nat := 4983230072969 + 3 ^ 40 * 7574226 * 2
def baseEnd_7574226 : Nat := 432135391531265337737975

theorem tailTrace_7574226 : CollatzResearch.WordTrace tailWord_7574226 prefixEnd_7574226 432135391531265337737975 := by
  unfold tailWord_7574226
  simp only [CollatzResearch.WordTrace]
  refine ⟨69063679364470062914789633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184169811638586834439439021 69063679364470062914789633)
  ·
    refine ⟨51797759523352547186092225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69063679364470062914789633 51797759523352547186092225)
    ·
      refine ⟨38848319642514410389569169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51797759523352547186092225 38848319642514410389569169)
      ·
        refine ⟨29136239731885807792176877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38848319642514410389569169 29136239731885807792176877)
        ·
          refine ⟨10926089899457177922066329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29136239731885807792176877 10926089899457177922066329)
          ·
            refine ⟨8194567424592883441549747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10926089899457177922066329 8194567424592883441549747)
            ·
              refine ⟨12291851136889325162324621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194567424592883441549747 12291851136889325162324621)
              ·
                refine ⟨4609444176333496935871733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12291851136889325162324621 4609444176333496935871733)
                ·
                  refine ⟨432135391531265337737975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4609444176333496935871733 432135391531265337737975)
                  ·
                    rfl

theorem cell23_7574226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_7574226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574226 prefixEnd_7574226 := by exact prefixLift 7574226
  have htrace : WordTrace (prefixWord ++ tailWord_7574226) baseStart_7574226 baseEnd_7574226 := by
    simpa [prefixWord, tailWord_7574226, baseEnd_7574226] using wordTrace_append hprefix tailTrace_7574226
  have hstable : (prefixWord ++ tailWord_7574226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574226).length < 2 ^ (prefixWord ++ tailWord_7574226).sum := by decide
  have hdescent : baseEnd_7574226 < baseStart_7574226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574279 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7574279 : Nat := 118140960795 + 7574279 * 2 ^ 59
def prefixEnd_7574279 : Nat := 4983230072969 + 3 ^ 40 * 7574279 * 2
def baseEnd_7574279 : Nat := 3889245738256076332279031

theorem tailTrace_7574279 : CollatzResearch.WordTrace tailWord_7574279 prefixEnd_7574279 3889245738256076332279031 := by
  unfold tailWord_7574279
  simp only [CollatzResearch.WordTrace]
  refine ⟨276256650526688241710837891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184171100351125494473891927 276256650526688241710837891)
  ·
    refine ⟨414384975790032362566256837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276256650526688241710837891 414384975790032362566256837)
    ·
      refine ⟨77697182960631067981173157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414384975790032362566256837 77697182960631067981173157)
      ·
        refine ⟨14568221805118325246469967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77697182960631067981173157 14568221805118325246469967)
        ·
          refine ⟨21852332707677487869704951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14568221805118325246469967 21852332707677487869704951)
          ·
            refine ⟨32778499061516231804557427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21852332707677487869704951 32778499061516231804557427)
            ·
              refine ⟨49167748592274347706836141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32778499061516231804557427 49167748592274347706836141)
              ·
                refine ⟨18437905722102880390063553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49167748592274347706836141 18437905722102880390063553)
                ·
                  refine ⟨13828429291577160292547665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18437905722102880390063553 13828429291577160292547665)
                  ·
                    refine ⟨10371321968682870219410749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13828429291577160292547665 10371321968682870219410749)
                    ·
                      refine ⟨3889245738256076332279031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371321968682870219410749 3889245738256076332279031)
                      ·
                        rfl

theorem cell23_7574279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7574279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574279 prefixEnd_7574279 := by exact prefixLift 7574279
  have htrace : WordTrace (prefixWord ++ tailWord_7574279) baseStart_7574279 baseEnd_7574279 := by
    simpa [prefixWord, tailWord_7574279, baseEnd_7574279] using wordTrace_append hprefix tailTrace_7574279
  have hstable : (prefixWord ++ tailWord_7574279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574279).length < 2 ^ (prefixWord ++ tailWord_7574279).sum := by decide
  have hdescent : baseEnd_7574279 < baseStart_7574279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574303 : List Nat := [1, 1, 2, 4, 2, 4, 2, 2, 1, 4]
def baseStart_7574303 : Nat := 118140960795 + 7574303 * 2 ^ 59
def prefixEnd_7574303 : Nat := 4983230072969 + 3 ^ 40 * 7574303 * 2
def baseEnd_7574303 : Nat := 1296419353930594746126307

theorem tailTrace_7574303 : CollatzResearch.WordTrace tailWord_7574303 prefixEnd_7574303 1296419353930594746126307 := by
  unfold tailWord_7574303
  simp only [CollatzResearch.WordTrace]
  refine ⟨276257525878601293809711563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184171683919067529206474375 276257525878601293809711563)
  ·
    refine ⟨414386288817901940714567345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276257525878601293809711563 414386288817901940714567345)
    ·
      refine ⟨310789716613426455535925509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414386288817901940714567345 310789716613426455535925509)
      ·
        refine ⟨58273071865017460412986033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310789716613426455535925509 58273071865017460412986033)
        ·
          refine ⟨43704803898763095309739525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58273071865017460412986033 43704803898763095309739525)
          ·
            refine ⟨8194650731018080370576161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43704803898763095309739525 8194650731018080370576161)
            ·
              refine ⟨6145988048263560277932121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8194650731018080370576161 6145988048263560277932121)
              ·
                refine ⟨4609491036197670208449091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6145988048263560277932121 4609491036197670208449091)
                ·
                  refine ⟨6914236554296505312673637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609491036197670208449091 6914236554296505312673637)
                  ·
                    refine ⟨1296419353930594746126307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6914236554296505312673637 1296419353930594746126307)
                    ·
                      rfl

theorem cell23_7574303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 1, 4].length) (baseStart_7574303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574303 prefixEnd_7574303 := by exact prefixLift 7574303
  have htrace : WordTrace (prefixWord ++ tailWord_7574303) baseStart_7574303 baseEnd_7574303 := by
    simpa [prefixWord, tailWord_7574303, baseEnd_7574303] using wordTrace_append hprefix tailTrace_7574303
  have hstable : (prefixWord ++ tailWord_7574303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574303).length < 2 ^ (prefixWord ++ tailWord_7574303).sum := by decide
  have hdescent : baseEnd_7574303 < baseStart_7574303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574309 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_7574309 : Nat := 118140960795 + 7574309 * 2 ^ 59
def prefixEnd_7574309 : Nat := 4983230072969 + 3 ^ 40 * 7574309 * 2
def baseEnd_7574309 : Nat := 3889261142675711214903893

theorem tailTrace_7574309 : CollatzResearch.WordTrace tailWord_7574309 prefixEnd_7574309 3889261142675711214903893 := by
  unfold tailWord_7574309
  simp only [CollatzResearch.WordTrace]
  refine ⟨276257744716579556834429981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184171829811053037889619987 276257744716579556834429981)
  ·
    refine ⟨103596654268717333812911243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276257744716579556834429981 103596654268717333812911243)
    ·
      refine ⟨155394981403076000719366865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103596654268717333812911243 155394981403076000719366865)
      ·
        refine ⟨116546236052307000539525149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155394981403076000719366865 116546236052307000539525149)
        ·
          refine ⟨43704838519615125202321931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116546236052307000539525149 43704838519615125202321931)
          ·
            refine ⟨65557257779422687803482897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43704838519615125202321931 65557257779422687803482897)
            ·
              refine ⟨49167943334567015852612173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65557257779422687803482897 49167943334567015852612173)
              ·
                refine ⟨18437978750462630944729565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49167943334567015852612173 18437978750462630944729565)
                ·
                  refine ⟨6914242031423486604273587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18437978750462630944729565 6914242031423486604273587)
                  ·
                    refine ⟨10371363047135229906410381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6914242031423486604273587 10371363047135229906410381)
                    ·
                      refine ⟨3889261142675711214903893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371363047135229906410381 3889261142675711214903893)
                      ·
                        rfl

theorem cell23_7574309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_7574309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574309 prefixEnd_7574309 := by exact prefixLift 7574309
  have htrace : WordTrace (prefixWord ++ tailWord_7574309) baseStart_7574309 baseEnd_7574309 := by
    simpa [prefixWord, tailWord_7574309, baseEnd_7574309] using wordTrace_append hprefix tailTrace_7574309
  have hstable : (prefixWord ++ tailWord_7574309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574309).length < 2 ^ (prefixWord ++ tailWord_7574309).sum := by decide
  have hdescent : baseEnd_7574309 < baseStart_7574309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574312 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7574312 : Nat := 118140960795 + 7574312 * 2 ^ 59
def prefixEnd_7574312 : Nat := 4983230072969 + 3 ^ 40 * 7574312 * 2
def baseEnd_7574312 : Nat := 1296420894372558234388793

theorem tailTrace_7574312 : CollatzResearch.WordTrace tailWord_7574312 prefixEnd_7574312 1296420894372558234388793 := by
  unfold tailWord_7574312
  simp only [CollatzResearch.WordTrace]
  refine ⟨138128927067784344173394595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184171902757045792231192793 138128927067784344173394595)
  ·
    refine ⟨207193390601676516260091893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138128927067784344173394595 207193390601676516260091893)
    ·
      refine ⟨19424380368907173399383615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 207193390601676516260091893 19424380368907173399383615)
      ·
        refine ⟨29136570553360760099075423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19424380368907173399383615 29136570553360760099075423)
        ·
          refine ⟨43704855830041140148613135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29136570553360760099075423 43704855830041140148613135)
          ·
            refine ⟨65557283745061710222919703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43704855830041140148613135 65557283745061710222919703)
            ·
              refine ⟨98335925617592565334379555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65557283745061710222919703 98335925617592565334379555)
              ·
                refine ⟨147503888426388848001569333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98335925617592565334379555 147503888426388848001569333)
                ·
                  refine ⟨13828489539973954500147125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147503888426388848001569333 13828489539973954500147125)
                  ·
                    refine ⟨1296420894372558234388793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13828489539973954500147125 1296420894372558234388793)
                    ·
                      rfl

theorem cell23_7574312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7574312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574312 prefixEnd_7574312 := by exact prefixLift 7574312
  have htrace : WordTrace (prefixWord ++ tailWord_7574312) baseStart_7574312 baseEnd_7574312 := by
    simpa [prefixWord, tailWord_7574312, baseEnd_7574312] using wordTrace_append hprefix tailTrace_7574312
  have hstable : (prefixWord ++ tailWord_7574312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574312).length < 2 ^ (prefixWord ++ tailWord_7574312).sum := by decide
  have hdescent : baseEnd_7574312 < baseStart_7574312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574315 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 4]
def baseStart_7574315 : Nat := 118140960795 + 7574315 * 2 ^ 59
def prefixEnd_7574315 : Nat := 4983230072969 + 3 ^ 40 * 7574315 * 2
def baseEnd_7574315 : Nat := 3889264223559638191428865

theorem tailTrace_7574315 : CollatzResearch.WordTrace tailWord_7574315 prefixEnd_7574315 3889264223559638191428865 := by
  unfold tailWord_7574315
  simp only [CollatzResearch.WordTrace]
  refine ⟨276257963554557819859148399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184171975703038546572765599 276257963554557819859148399)
  ·
    refine ⟨414386945331836729788722599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276257963554557819859148399 414386945331836729788722599)
    ·
      refine ⟨621580417997755094683083899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414386945331836729788722599 621580417997755094683083899)
      ·
        refine ⟨932370626996632642024625849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621580417997755094683083899 932370626996632642024625849)
        ·
          refine ⟨699277970247474481518469387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932370626996632642024625849 699277970247474481518469387)
          ·
            refine ⟨1048916955371211722277704081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699277970247474481518469387 1048916955371211722277704081)
            ·
              refine ⟨786687716528408791708278061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1048916955371211722277704081 786687716528408791708278061)
              ·
                refine ⟨295007893698153296890604273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 786687716528408791708278061 295007893698153296890604273)
                ·
                  refine ⟨221255920273614972667953205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 295007893698153296890604273 221255920273614972667953205)
                  ·
                    refine ⟨20742742525651403687620613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 221255920273614972667953205 20742742525651403687620613)
                    ·
                      refine ⟨3889264223559638191428865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20742742525651403687620613 3889264223559638191428865)
                      ·
                        rfl

theorem cell23_7574315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 4].length) (baseStart_7574315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574315 prefixEnd_7574315 := by exact prefixLift 7574315
  have htrace : WordTrace (prefixWord ++ tailWord_7574315) baseStart_7574315 baseEnd_7574315 := by
    simpa [prefixWord, tailWord_7574315, baseEnd_7574315] using wordTrace_append hprefix tailTrace_7574315
  have hstable : (prefixWord ++ tailWord_7574315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574315).length < 2 ^ (prefixWord ++ tailWord_7574315).sum := by decide
  have hdescent : baseEnd_7574315 < baseStart_7574315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574359 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 4, 4]
def baseStart_7574359 : Nat := 118140960795 + 7574359 * 2 ^ 59
def prefixEnd_7574359 : Nat := 4983230072969 + 3 ^ 40 * 7574359 * 2
def baseEnd_7574359 : Nat := 1296428938902812006426221

theorem tailTrace_7574359 : CollatzResearch.WordTrace tailWord_7574359 prefixEnd_7574359 1296428938902812006426221 := by
  unfold tailWord_7574359
  simp only [CollatzResearch.WordTrace]
  refine ⟨276259568366398415373750131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184173045577598943582500087 276259568366398415373750131)
  ·
    refine ⟨414389352549597623060625197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276259568366398415373750131 414389352549597623060625197)
    ·
      refine ⟨155396007206099108647734449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414389352549597623060625197 155396007206099108647734449)
      ·
        refine ⟨116547005404574331485800837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155396007206099108647734449 116547005404574331485800837)
        ·
          refine ⟨21852563513357687153587657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116547005404574331485800837 21852563513357687153587657)
          ·
            refine ⟨16389422635018265365190743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21852563513357687153587657 16389422635018265365190743)
            ·
              refine ⟨24584133952527398047786115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16389422635018265365190743 24584133952527398047786115)
              ·
                refine ⟨36876200928791097071679173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24584133952527398047786115 36876200928791097071679173)
                ·
                  refine ⟨6914287674148330700939845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36876200928791097071679173 6914287674148330700939845)
                  ·
                    refine ⟨1296428938902812006426221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6914287674148330700939845 1296428938902812006426221)
                    ·
                      rfl

theorem cell23_7574359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_7574359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574359 prefixEnd_7574359 := by exact prefixLift 7574359
  have htrace : WordTrace (prefixWord ++ tailWord_7574359) baseStart_7574359 baseEnd_7574359 := by
    simpa [prefixWord, tailWord_7574359, baseEnd_7574359] using wordTrace_append hprefix tailTrace_7574359
  have hstable : (prefixWord ++ tailWord_7574359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574359).length < 2 ^ (prefixWord ++ tailWord_7574359).sum := by decide
  have hdescent : baseEnd_7574359 < baseStart_7574359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574389 : List Nat := [1, 3, 4, 1, 1, 2, 4, 7]
def baseStart_7574389 : Nat := 118140960795 + 7574389 * 2 ^ 59
def prefixEnd_7574389 : Nat := 4983230072969 + 3 ^ 40 * 7574389 * 2
def baseEnd_7574389 : Nat := 144048230412150774144575

theorem tailTrace_7574389 : CollatzResearch.WordTrace tailWord_7574389 prefixEnd_7574389 144048230412150774144575 := by
  unfold tailWord_7574389
  simp only [CollatzResearch.WordTrace]
  refine ⟨276260662556289730497342221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184173775037526486998228147 276260662556289730497342221)
  ·
    refine ⟨103597748458608648936503333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276260662556289730497342221 103597748458608648936503333)
    ·
      refine ⟨19424577835989121675594375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103597748458608648936503333 19424577835989121675594375)
      ·
        refine ⟨29136866753983682513391563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19424577835989121675594375 29136866753983682513391563)
        ·
          refine ⟨43705300130975523770087345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29136866753983682513391563 43705300130975523770087345)
          ·
            refine ⟨32778975098231642827565509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43705300130975523770087345 32778975098231642827565509)
            ·
              refine ⟨6146057830918433030168533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32778975098231642827565509 6146057830918433030168533)
              ·
                refine ⟨144048230412150774144575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6146057830918433030168533 144048230412150774144575)
                ·
                  rfl

theorem cell23_7574389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 7].length) (baseStart_7574389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574389 prefixEnd_7574389 := by exact prefixLift 7574389
  have htrace : WordTrace (prefixWord ++ tailWord_7574389) baseStart_7574389 baseEnd_7574389 := by
    simpa [prefixWord, tailWord_7574389, baseEnd_7574389] using wordTrace_append hprefix tailTrace_7574389
  have hstable : (prefixWord ++ tailWord_7574389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574389).length < 2 ^ (prefixWord ++ tailWord_7574389).sum := by decide
  have hdescent : baseEnd_7574389 < baseStart_7574389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574399 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 3]
def baseStart_7574399 : Nat := 118140960795 + 7574399 * 2 ^ 59
def prefixEnd_7574399 : Nat := 4983230072969 + 3 ^ 40 * 7574399 * 2
def baseEnd_7574399 : Nat := 3889307355934615862778479

theorem tailTrace_7574399 : CollatzResearch.WordTrace tailWord_7574399 prefixEnd_7574399 3889307355934615862778479 := by
  unfold tailWord_7574399
  simp only [CollatzResearch.WordTrace]
  refine ⟨276261027286253502205206251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184174018190835668136804167 276261027286253502205206251)
  ·
    refine ⟨414391540929380253307809377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276261027286253502205206251 414391540929380253307809377)
    ·
      refine ⟨310793655697035189980857033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414391540929380253307809377 310793655697035189980857033)
      ·
        refine ⟨233095241772776392485642775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310793655697035189980857033 233095241772776392485642775)
        ·
          refine ⟨349642862659164588728464163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233095241772776392485642775 349642862659164588728464163)
          ·
            refine ⟨524464293988746883092696245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349642862659164588728464163 524464293988746883092696245)
            ·
              refine ⟨49168527561445020289940273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 524464293988746883092696245 49168527561445020289940273)
              ·
                refine ⟨36876395671083765217455205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49168527561445020289940273 36876395671083765217455205)
                ·
                  refine ⟨6914324188328205978272851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36876395671083765217455205 6914324188328205978272851)
                  ·
                    refine ⟨10371486282492308967409277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6914324188328205978272851 10371486282492308967409277)
                    ·
                      refine ⟨3889307355934615862778479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371486282492308967409277 3889307355934615862778479)
                      ·
                        rfl

theorem cell23_7574399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_7574399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574399 prefixEnd_7574399 := by exact prefixLift 7574399
  have htrace : WordTrace (prefixWord ++ tailWord_7574399) baseStart_7574399 baseEnd_7574399 := by
    simpa [prefixWord, tailWord_7574399, baseEnd_7574399] using wordTrace_append hprefix tailTrace_7574399
  have hstable : (prefixWord ++ tailWord_7574399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574399).length < 2 ^ (prefixWord ++ tailWord_7574399).sum := by decide
  have hdescent : baseEnd_7574399 < baseStart_7574399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574432 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 2, 6]
def baseStart_7574432 : Nat := 118140960795 + 7574432 * 2 ^ 59
def prefixEnd_7574432 : Nat := 4983230072969 + 3 ^ 40 * 7574432 * 2
def baseEnd_7574432 : Nat := 1296441433598738077888609

theorem tailTrace_7574432 : CollatzResearch.WordTrace tailWord_7574432 prefixEnd_7574432 1296441433598738077888609 := by
  unfold tailWord_7574432
  simp only [CollatzResearch.WordTrace]
  refine ⟨138131115447566974420578775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184174820596755965894105033 138131115447566974420578775)
  ·
    refine ⟨207196673171350461630868163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138131115447566974420578775 207196673171350461630868163)
    ·
      refine ⟨310795009757025692446302245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207196673171350461630868163 310795009757025692446302245)
      ·
        refine ⟨58274064329442317333681671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310795009757025692446302245 58274064329442317333681671)
        ·
          refine ⟨87411096494163476000522507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58274064329442317333681671 87411096494163476000522507)
          ·
            refine ⟨131116644741245214000783761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87411096494163476000522507 131116644741245214000783761)
            ·
              refine ⟨98337483555933910500587821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131116644741245214000783761 98337483555933910500587821)
              ·
                refine ⟨36876556333475216437720433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98337483555933910500587821 36876556333475216437720433)
                ·
                  refine ⟨27657417250106412328290325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36876556333475216437720433 27657417250106412328290325)
                  ·
                    refine ⟨1296441433598738077888609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27657417250106412328290325 1296441433598738077888609)
                    ·
                      rfl

theorem cell23_7574432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_7574432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574432 prefixEnd_7574432 := by exact prefixLift 7574432
  have htrace : WordTrace (prefixWord ++ tailWord_7574432) baseStart_7574432 baseEnd_7574432 := by
    simpa [prefixWord, tailWord_7574432, baseEnd_7574432] using wordTrace_append hprefix tailTrace_7574432
  have hstable : (prefixWord ++ tailWord_7574432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574432).length < 2 ^ (prefixWord ++ tailWord_7574432).sum := by decide
  have hdescent : baseEnd_7574432 < baseStart_7574432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574433 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7574433 : Nat := 118140960795 + 7574433 * 2 ^ 59
def prefixEnd_7574433 : Nat := 4983230072969 + 3 ^ 40 * 7574433 * 2
def baseEnd_7574433 : Nat := 3889324814276868729753323

theorem tailTrace_7574433 : CollatzResearch.WordTrace tailWord_7574433 prefixEnd_7574433 3889324814276868729753323 := by
  unfold tailWord_7574433
  simp only [CollatzResearch.WordTrace]
  refine ⟨276262267368130326011943953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184174844912086884007962635 276262267368130326011943953)
  ·
    refine ⟨207196700526097744508957965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276262267368130326011943953 207196700526097744508957965)
    ·
      refine ⟨77698762697286654190859237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207196700526097744508957965 77698762697286654190859237)
      ·
        refine ⟨14568518005741247660786107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77698762697286654190859237 14568518005741247660786107)
        ·
          refine ⟨21852777008611871491179161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14568518005741247660786107 21852777008611871491179161)
          ·
            refine ⟨16389582756458903618384371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21852777008611871491179161 16389582756458903618384371)
            ·
              refine ⟨24584374134688355427576557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16389582756458903618384371 24584374134688355427576557)
              ·
                refine ⟨9219140300508133285341209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24584374134688355427576557 9219140300508133285341209)
                ·
                  refine ⟨6914355225381099964005907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9219140300508133285341209 6914355225381099964005907)
                  ·
                    refine ⟨10371532838071649946008861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6914355225381099964005907 10371532838071649946008861)
                    ·
                      refine ⟨3889324814276868729753323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371532838071649946008861 3889324814276868729753323)
                      ·
                        rfl

theorem cell23_7574433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7574433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574433 prefixEnd_7574433 := by exact prefixLift 7574433
  have htrace : WordTrace (prefixWord ++ tailWord_7574433) baseStart_7574433 baseEnd_7574433 := by
    simpa [prefixWord, tailWord_7574433, baseEnd_7574433] using wordTrace_append hprefix tailTrace_7574433
  have hstable : (prefixWord ++ tailWord_7574433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574433).length < 2 ^ (prefixWord ++ tailWord_7574433).sum := by decide
  have hdescent : baseEnd_7574433 < baseStart_7574433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574454 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7574454 : Nat := 118140960795 + 7574454 * 2 ^ 59
def prefixEnd_7574454 : Nat := 4983230072969 + 3 ^ 40 * 7574454 * 2
def baseEnd_7574454 : Nat := 3889335597370613147590727

theorem tailTrace_7574454 : CollatzResearch.WordTrace tailWord_7574454 prefixEnd_7574454 3889335597370613147590727 := by
  unfold tailWord_7574454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266439581315890412403651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184175355534036164398972277 17266439581315890412403651)
  ·
    refine ⟨25899659371973835618605477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17266439581315890412403651 25899659371973835618605477)
    ·
      refine ⟨4856186132245094178488527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25899659371973835618605477 4856186132245094178488527)
      ·
        refine ⟨7284279198367641267732791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856186132245094178488527 7284279198367641267732791)
        ·
          refine ⟨10926418797551461901599187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7284279198367641267732791 10926418797551461901599187)
          ·
            refine ⟨16389628196327192852398781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10926418797551461901599187 16389628196327192852398781)
            ·
              refine ⟨6146110573622697319649543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16389628196327192852398781 6146110573622697319649543)
              ·
                refine ⟨9219165860434045979474315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146110573622697319649543 9219165860434045979474315)
                ·
                  refine ⟨13828748790651068969211473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9219165860434045979474315 13828748790651068969211473)
                  ·
                    refine ⟨10371561592988301726908605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13828748790651068969211473 10371561592988301726908605)
                    ·
                      refine ⟨3889335597370613147590727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371561592988301726908605 3889335597370613147590727)
                      ·
                        rfl

theorem cell23_7574454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7574454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574454 prefixEnd_7574454 := by exact prefixLift 7574454
  have htrace : WordTrace (prefixWord ++ tailWord_7574454) baseStart_7574454 baseEnd_7574454 := by
    simpa [prefixWord, tailWord_7574454, baseEnd_7574454] using wordTrace_append hprefix tailTrace_7574454
  have hstable : (prefixWord ++ tailWord_7574454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574454).length < 2 ^ (prefixWord ++ tailWord_7574454).sum := by decide
  have hdescent : baseEnd_7574454 < baseStart_7574454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574456 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 1, 4, 2]
def baseStart_7574456 : Nat := 118140960795 + 7574456 * 2 ^ 59
def prefixEnd_7574456 : Nat := 4983230072969 + 3 ^ 40 * 7574456 * 2
def baseEnd_7574456 : Nat := 3889336624331922139765717

theorem tailTrace_7574456 : CollatzResearch.WordTrace tailWord_7574456 prefixEnd_7574456 3889336624331922139765717 := by
  unfold tailWord_7574456
  simp only [CollatzResearch.WordTrace]
  refine ⟨138131553123523500470015611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184175404164698000626687481 138131553123523500470015611)
  ·
    refine ⟨207197329685285250705023417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138131553123523500470015611 207197329685285250705023417)
    ·
      refine ⟨155397997263963938028767563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207197329685285250705023417 155397997263963938028767563)
      ·
        refine ⟨233096995895945907043151345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155397997263963938028767563 233096995895945907043151345)
        ·
          refine ⟨174822746921959430282363509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233096995895945907043151345 174822746921959430282363509)
          ·
            refine ⟨16389632523933696588971579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174822746921959430282363509 16389632523933696588971579)
            ·
              refine ⟨24584448785900544883457369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16389632523933696588971579 24584448785900544883457369)
              ·
                refine ⟨18438336589425408662593027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24584448785900544883457369 18438336589425408662593027)
                ·
                  refine ⟨27657504884138112993889541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18438336589425408662593027 27657504884138112993889541)
                  ·
                    refine ⟨5185782165775896186354289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27657504884138112993889541 5185782165775896186354289)
                    ·
                      refine ⟨3889336624331922139765717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185782165775896186354289 3889336624331922139765717)
                      ·
                        rfl

theorem cell23_7574456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_7574456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574456 prefixEnd_7574456 := by exact prefixLift 7574456
  have htrace : WordTrace (prefixWord ++ tailWord_7574456) baseStart_7574456 baseEnd_7574456 := by
    simpa [prefixWord, tailWord_7574456, baseEnd_7574456] using wordTrace_append hprefix tailTrace_7574456
  have hstable : (prefixWord ++ tailWord_7574456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574456).length < 2 ^ (prefixWord ++ tailWord_7574456).sum := by decide
  have hdescent : baseEnd_7574456 < baseStart_7574456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574486 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7574486 : Nat := 118140960795 + 7574486 * 2 ^ 59
def prefixEnd_7574486 : Nat := 4983230072969 + 3 ^ 40 * 7574486 * 2
def baseEnd_7574486 : Nat := 3889352028751557022390579

theorem tailTrace_7574486 : CollatzResearch.WordTrace tailWord_7574486 prefixEnd_7574486 3889352028751557022390579 := by
  unfold tailWord_7574486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266512527308644753976457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184176133624625544042415541 17266512527308644753976457)
  ·
    refine ⟨12949884395481483565482343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17266512527308644753976457 12949884395481483565482343)
    ·
      refine ⟨19424826593222225348223515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12949884395481483565482343 19424826593222225348223515)
      ·
        refine ⟨29137239889833338022335273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19424826593222225348223515 29137239889833338022335273)
        ·
          refine ⟨21852929917375003516751455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29137239889833338022335273 21852929917375003516751455)
          ·
            refine ⟨32779394876062505275127183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21852929917375003516751455 32779394876062505275127183)
            ·
              refine ⟨49169092314093757912690775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32779394876062505275127183 49169092314093757912690775)
              ·
                refine ⟨73753638471140636869036163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49169092314093757912690775 73753638471140636869036163)
                ·
                  refine ⟨110630457706710955303554245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73753638471140636869036163 110630457706710955303554245)
                  ·
                    refine ⟨20743210820008304119416421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110630457706710955303554245 20743210820008304119416421)
                    ·
                      refine ⟨3889352028751557022390579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20743210820008304119416421 3889352028751557022390579)
                      ·
                        rfl

theorem cell23_7574486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7574486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574486 prefixEnd_7574486 := by exact prefixLift 7574486
  have htrace : WordTrace (prefixWord ++ tailWord_7574486) baseStart_7574486 baseEnd_7574486 := by
    simpa [prefixWord, tailWord_7574486, baseEnd_7574486] using wordTrace_append hprefix tailTrace_7574486
  have hstable : (prefixWord ++ tailWord_7574486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574486).length < 2 ^ (prefixWord ++ tailWord_7574486).sum := by decide
  have hdescent : baseEnd_7574486 < baseStart_7574486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574489 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 3]
def baseStart_7574489 : Nat := 118140960795 + 7574489 * 2 ^ 59
def prefixEnd_7574489 : Nat := 4983230072969 + 3 ^ 40 * 7574489 * 2
def baseEnd_7574489 : Nat := 3889353569193520510653065

theorem tailTrace_7574489 : CollatzResearch.WordTrace tailWord_7574489 prefixEnd_7574489 3889353569193520510653065 := by
  unfold tailWord_7574489
  simp only [CollatzResearch.WordTrace]
  refine ⟨276264309855927447575982521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184176206570618298383988347 276264309855927447575982521)
  ·
    refine ⟨207198232391945585681986891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276264309855927447575982521 207198232391945585681986891)
    ·
      refine ⟨310797348587918378522980337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207198232391945585681986891 310797348587918378522980337)
      ·
        refine ⟨233098011440938783892235253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310797348587918378522980337 233098011440938783892235253)
        ·
          refine ⟨21852938572588010989897055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233098011440938783892235253 21852938572588010989897055)
          ·
            refine ⟨32779407858882016484845583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21852938572588010989897055 32779407858882016484845583)
            ·
              refine ⟨49169111788323024727268375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32779407858882016484845583 49169111788323024727268375)
              ·
                refine ⟨73753667682484537090902563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49169111788323024727268375 73753667682484537090902563)
                ·
                  refine ⟨110630501523726805636353845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73753667682484537090902563 110630501523726805636353845)
                  ·
                    refine ⟨10371609517849388028408173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110630501523726805636353845 10371609517849388028408173)
                    ·
                      refine ⟨3889353569193520510653065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371609517849388028408173 3889353569193520510653065)
                      ·
                        rfl

theorem cell23_7574489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_7574489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574489 prefixEnd_7574489 := by exact prefixLift 7574489
  have htrace : WordTrace (prefixWord ++ tailWord_7574489) baseStart_7574489 baseEnd_7574489 := by
    simpa [prefixWord, tailWord_7574489, baseEnd_7574489] using wordTrace_append hprefix tailTrace_7574489
  have hstable : (prefixWord ++ tailWord_7574489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574489).length < 2 ^ (prefixWord ++ tailWord_7574489).sum := by decide
  have hdescent : baseEnd_7574489 < baseStart_7574489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574522 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_7574522 : Nat := 118140960795 + 7574522 * 2 ^ 59
def prefixEnd_7574522 : Nat := 4983230072969 + 3 ^ 40 * 7574522 * 2
def baseEnd_7574522 : Nat := 1296456838018372960513471

theorem tailTrace_7574522 : CollatzResearch.WordTrace tailWord_7574522 prefixEnd_7574522 1296456838018372960513471 := by
  unfold tailWord_7574522
  simp only [CollatzResearch.WordTrace]
  refine ⟨69066378366201973552983455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184177008976538596141289213 69066378366201973552983455)
  ·
    refine ⟨103599567549302960329475183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69066378366201973552983455 103599567549302960329475183)
    ·
      refine ⟨155399351323954440494212775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103599567549302960329475183 155399351323954440494212775)
      ·
        refine ⟨233099026985931660741319163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155399351323954440494212775 233099026985931660741319163)
        ·
          refine ⟨349648540478897491111978745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233099026985931660741319163 349648540478897491111978745)
          ·
            refine ⟨262236405359173118333984059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349648540478897491111978745 262236405359173118333984059)
            ·
              refine ⟨393354608038759677500976089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262236405359173118333984059 393354608038759677500976089)
              ·
                refine ⟨295015956029069758125732067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 393354608038759677500976089 295015956029069758125732067)
                ·
                  refine ⟨442523934043604637188598101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295015956029069758125732067 442523934043604637188598101)
                  ·
                    refine ⟨1296456838018372960513471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 442523934043604637188598101 1296456838018372960513471)
                    ·
                      rfl

theorem cell23_7574522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_7574522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574522 prefixEnd_7574522 := by exact prefixLift 7574522
  have htrace : WordTrace (prefixWord ++ tailWord_7574522) baseStart_7574522 baseEnd_7574522 := by
    simpa [prefixWord, tailWord_7574522, baseEnd_7574522] using wordTrace_append hprefix tailTrace_7574522
  have hstable : (prefixWord ++ tailWord_7574522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574522).length < 2 ^ (prefixWord ++ tailWord_7574522).sum := by decide
  have hdescent : baseEnd_7574522 < baseStart_7574522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574590 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_7574590 : Nat := 118140960795 + 7574590 * 2 ^ 59
def prefixEnd_7574590 : Nat := 4983230072969 + 3 ^ 40 * 7574590 * 2
def baseEnd_7574590 : Nat := 1296468476913208205163367

theorem tailTrace_7574590 : CollatzResearch.WordTrace tailWord_7574590 prefixEnd_7574590 1296468476913208205163367 := by
  unfold tailWord_7574590
  simp only [CollatzResearch.WordTrace]
  refine ⟨34533499203570192728176153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184178662419041027883606149 34533499203570192728176153)
  ·
    refine ⟨25900124402677644546132115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34533499203570192728176153 25900124402677644546132115)
    ·
      refine ⟨38850186604016466819198173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25900124402677644546132115 38850186604016466819198173)
      ·
        refine ⟨14568819976506175057199315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38850186604016466819198173 14568819976506175057199315)
        ·
          refine ⟨21853229964759262585798973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14568819976506175057199315 21853229964759262585798973)
          ·
            refine ⟨8194961236784723469674615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21853229964759262585798973 8194961236784723469674615)
            ·
              refine ⟨12292441855177085204511923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8194961236784723469674615 12292441855177085204511923)
              ·
                refine ⟨18438662782765627806767885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12292441855177085204511923 18438662782765627806767885)
                ·
                  refine ⟨6914498543537110427537957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18438662782765627806767885 6914498543537110427537957)
                  ·
                    refine ⟨1296468476913208205163367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6914498543537110427537957 1296468476913208205163367)
                    ·
                      rfl

theorem cell23_7574590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_7574590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574590 prefixEnd_7574590 := by exact prefixLift 7574590
  have htrace : WordTrace (prefixWord ++ tailWord_7574590) baseStart_7574590 baseEnd_7574590 := by
    simpa [prefixWord, tailWord_7574590, baseEnd_7574590] using wordTrace_append hprefix tailTrace_7574590
  have hstable : (prefixWord ++ tailWord_7574590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574590).length < 2 ^ (prefixWord ++ tailWord_7574590).sum := by decide
  have hdescent : baseEnd_7574590 < baseStart_7574590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574623 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 2, 3, 2]
def baseStart_7574623 : Nat := 118140960795 + 7574623 * 2 ^ 59
def prefixEnd_7574623 : Nat := 4983230072969 + 3 ^ 40 * 7574623 * 2
def baseEnd_7574623 : Nat := 3889422375601222986377449

theorem tailTrace_7574623 : CollatzResearch.WordTrace tailWord_7574623 prefixEnd_7574623 3889422375601222986377449 := by
  unfold tailWord_7574623
  simp only [CollatzResearch.WordTrace]
  refine ⟨276269197237441988461360523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184179464824961325640907015 276269197237441988461360523)
  ·
    refine ⟨414403795856162982692040785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276269197237441988461360523 414403795856162982692040785)
    ·
      refine ⟨310802846892122237019030589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414403795856162982692040785 310802846892122237019030589)
      ·
        refine ⟨116551067584545838882136471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310802846892122237019030589 116551067584545838882136471)
        ·
          refine ⟨174826601376818758323204707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116551067584545838882136471 174826601376818758323204707)
          ·
            refine ⟨262239902065228137484807061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174826601376818758323204707 262239902065228137484807061)
            ·
              refine ⟨12292495409307568944600331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 262239902065228137484807061 12292495409307568944600331)
              ·
                refine ⟨18438743113961353416900497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12292495409307568944600331 18438743113961353416900497)
                ·
                  refine ⟨13829057335471015062675373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18438743113961353416900497 13829057335471015062675373)
                  ·
                    refine ⟨5185896500801630648503265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13829057335471015062675373 5185896500801630648503265)
                    ·
                      refine ⟨3889422375601222986377449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185896500801630648503265 3889422375601222986377449)
                      ·
                        rfl

theorem cell23_7574623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_7574623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574623 prefixEnd_7574623 := by exact prefixLift 7574623
  have htrace : WordTrace (prefixWord ++ tailWord_7574623) baseStart_7574623 baseEnd_7574623 := by
    simpa [prefixWord, tailWord_7574623, baseEnd_7574623] using wordTrace_append hprefix tailTrace_7574623
  have hstable : (prefixWord ++ tailWord_7574623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574623).length < 2 ^ (prefixWord ++ tailWord_7574623).sum := by decide
  have hdescent : baseEnd_7574623 < baseStart_7574623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574633 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 1, 5]
def baseStart_7574633 : Nat := 118140960795 + 7574633 * 2 ^ 59
def prefixEnd_7574633 : Nat := 4983230072969 + 3 ^ 40 * 7574633 * 2
def baseEnd_7574633 : Nat := 1296475836802589315750801

theorem tailTrace_7574633 : CollatzResearch.WordTrace tailWord_7574633 prefixEnd_7574633 1296475836802589315750801 := by
  unfold tailWord_7574633
  simp only [CollatzResearch.WordTrace]
  refine ⟨276269561967405760169224553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184179707978270506779483035 276269561967405760169224553)
  ·
    refine ⟨207202171475554320126918415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276269561967405760169224553 207202171475554320126918415)
    ·
      refine ⟨310803257213331480190377623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207202171475554320126918415 310803257213331480190377623)
      ·
        refine ⟨466204885819997220285566435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310803257213331480190377623 466204885819997220285566435)
        ·
          refine ⟨699307328729995830428349653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466204885819997220285566435 699307328729995830428349653)
          ·
            refine ⟨16390015517109277275664445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 699307328729995830428349653 16390015517109277275664445)
            ·
              refine ⟨6146255818915978978374167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16390015517109277275664445 6146255818915978978374167)
              ·
                refine ⟨9219383728373968467561251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146255818915978978374167 9219383728373968467561251)
                ·
                  refine ⟨13829075592560952701341877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9219383728373968467561251 13829075592560952701341877)
                  ·
                    refine ⟨1296475836802589315750801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13829075592560952701341877 1296475836802589315750801)
                    ·
                      rfl

theorem cell23_7574633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 1, 5].length) (baseStart_7574633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574633 prefixEnd_7574633 := by exact prefixLift 7574633
  have htrace : WordTrace (prefixWord ++ tailWord_7574633) baseStart_7574633 baseEnd_7574633 := by
    simpa [prefixWord, tailWord_7574633, baseEnd_7574633] using wordTrace_append hprefix tailTrace_7574633
  have hstable : (prefixWord ++ tailWord_7574633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574633).length < 2 ^ (prefixWord ++ tailWord_7574633).sum := by decide
  have hdescent : baseEnd_7574633 < baseStart_7574633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574646 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_7574646 : Nat := 118140960795 + 7574646 * 2 ^ 59
def prefixEnd_7574646 : Nat := 4983230072969 + 3 ^ 40 * 7574646 * 2
def baseEnd_7574646 : Nat := 1296478061885425465463281

theorem tailTrace_7574646 : CollatzResearch.WordTrace tailWord_7574646 prefixEnd_7574646 1296478061885425465463281 := by
  unfold tailWord_7574646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266877257272416461840487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184180024077572442259631861 17266877257272416461840487)
  ·
    refine ⟨25900315885908624692760731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17266877257272416461840487 25900315885908624692760731)
    ·
      refine ⟨38850473828862937039141097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25900315885908624692760731 38850473828862937039141097)
      ·
        refine ⟨29137855371647202779355823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38850473828862937039141097 29137855371647202779355823)
        ·
          refine ⟨43706783057470804169033735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29137855371647202779355823 43706783057470804169033735)
          ·
            refine ⟨65560174586206206253550603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43706783057470804169033735 65560174586206206253550603)
            ·
              refine ⟨98340261879309309380325905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65560174586206206253550603 98340261879309309380325905)
              ·
                refine ⟨73755196409481982035244429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98340261879309309380325905 73755196409481982035244429)
                ·
                  refine ⟨27658198653555743263216661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73755196409481982035244429 27658198653555743263216661)
                  ·
                    refine ⟨1296478061885425465463281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27658198653555743263216661 1296478061885425465463281)
                    ·
                      rfl

theorem cell23_7574646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_7574646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574646 prefixEnd_7574646 := by exact prefixLift 7574646
  have htrace : WordTrace (prefixWord ++ tailWord_7574646) baseStart_7574646 baseEnd_7574646 := by
    simpa [prefixWord, tailWord_7574646, baseEnd_7574646] using wordTrace_append hprefix tailTrace_7574646
  have hstable : (prefixWord ++ tailWord_7574646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574646).length < 2 ^ (prefixWord ++ tailWord_7574646).sum := by decide
  have hdescent : baseEnd_7574646 < baseStart_7574646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574656 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 3]
def baseStart_7574656 : Nat := 118140960795 + 7574656 * 2 ^ 59
def prefixEnd_7574656 : Nat := 4983230072969 + 3 ^ 40 * 7574656 * 2
def baseEnd_7574656 : Nat := 3889439320462821357264797

theorem tailTrace_7574656 : CollatzResearch.WordTrace tailWord_7574656 prefixEnd_7574656 3889439320462821357264797 := by
  unfold tailWord_7574656
  simp only [CollatzResearch.WordTrace]
  refine ⟨138135200423161217548655911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184180267230881623398207881 138135200423161217548655911)
  ·
    refine ⟨207202800634741826322983867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138135200423161217548655911 207202800634741826322983867)
    ·
      refine ⟨310804200952112739484475801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207202800634741826322983867 310804200952112739484475801)
      ·
        refine ⟨233103150714084554613356851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310804200952112739484475801 233103150714084554613356851)
        ·
          refine ⟨349654726071126831920035277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233103150714084554613356851 349654726071126831920035277)
          ·
            refine ⟨131120522276672561970013229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349654726071126831920035277 131120522276672561970013229)
            ·
              refine ⟨49170195853752210738754961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131120522276672561970013229 49170195853752210738754961)
              ·
                refine ⟨36877646890314158054066221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49170195853752210738754961 36877646890314158054066221)
                ·
                  refine ⟨13829117583867809270274833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36877646890314158054066221 13829117583867809270274833)
                  ·
                    refine ⟨10371838187900856952706125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13829117583867809270274833 10371838187900856952706125)
                    ·
                      refine ⟨3889439320462821357264797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371838187900856952706125 3889439320462821357264797)
                      ·
                        rfl

theorem cell23_7574656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_7574656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574656 prefixEnd_7574656 := by exact prefixLift 7574656
  have htrace : WordTrace (prefixWord ++ tailWord_7574656) baseStart_7574656 baseEnd_7574656 := by
    simpa [prefixWord, tailWord_7574656, baseEnd_7574656] using wordTrace_append hprefix tailTrace_7574656
  have hstable : (prefixWord ++ tailWord_7574656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574656).length < 2 ^ (prefixWord ++ tailWord_7574656).sum := by decide
  have hdescent : baseEnd_7574656 < baseStart_7574656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574670 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_7574670 : Nat := 118140960795 + 7574670 * 2 ^ 59
def prefixEnd_7574670 : Nat := 4983230072969 + 3 ^ 40 * 7574670 * 2
def baseEnd_7574670 : Nat := 3889446509191984302489733

theorem tailTrace_7574670 : CollatzResearch.WordTrace tailWord_7574670 prefixEnd_7574670 3889446509191984302489733 := by
  unfold tailWord_7574670
  simp only [CollatzResearch.WordTrace]
  refine ⟨34533863933533964436040183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184180607645514476992214309 34533863933533964436040183)
  ·
    refine ⟨51800795900300946654060275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34533863933533964436040183 51800795900300946654060275)
    ·
      refine ⟨77701193850451419981090413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51800795900300946654060275 77701193850451419981090413)
      ·
        refine ⟨29137947693919282492908905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77701193850451419981090413 29137947693919282492908905)
        ·
          refine ⟨21853460770439461869681679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29137947693919282492908905 21853460770439461869681679)
          ·
            refine ⟨32780191155659192804522519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21853460770439461869681679 32780191155659192804522519)
            ·
              refine ⟨49170286733488789206783779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32780191155659192804522519 49170286733488789206783779)
              ·
                refine ⟨73755430100233183810175669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49170286733488789206783779 73755430100233183810175669)
                ·
                  refine ⟨6914571571896860982203969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73755430100233183810175669 6914571571896860982203969)
                  ·
                    refine ⟨5185928678922645736652977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6914571571896860982203969 5185928678922645736652977)
                    ·
                      refine ⟨3889446509191984302489733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185928678922645736652977 3889446509191984302489733)
                      ·
                        rfl

theorem cell23_7574670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_7574670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574670 prefixEnd_7574670 := by exact prefixLift 7574670
  have htrace : WordTrace (prefixWord ++ tailWord_7574670) baseStart_7574670 baseEnd_7574670 := by
    simpa [prefixWord, tailWord_7574670, baseEnd_7574670] using wordTrace_append hprefix tailTrace_7574670
  have hstable : (prefixWord ++ tailWord_7574670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574670).length < 2 ^ (prefixWord ++ tailWord_7574670).sum := by decide
  have hdescent : baseEnd_7574670 < baseStart_7574670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574687 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7574687 : Nat := 118140960795 + 7574687 * 2 ^ 59
def prefixEnd_7574687 : Nat := 4983230072969 + 3 ^ 40 * 7574687 * 2
def baseEnd_7574687 : Nat := 3889455238363110735977155

theorem tailTrace_7574687 : CollatzResearch.WordTrace tailWord_7574687 prefixEnd_7574687 3889455238363110735977155 := by
  unfold tailWord_7574687
  simp only [CollatzResearch.WordTrace]
  refine ⟨276271531509210127391690315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184181021006140084927793543 276271531509210127391690315)
  ·
    refine ⟨414407297263815191087535473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276271531509210127391690315 414407297263815191087535473)
    ·
      refine ⟨310805472947861393315651605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414407297263815191087535473 310805472947861393315651605)
      ·
        refine ⟨14569006544431002811671169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 310805472947861393315651605 14569006544431002811671169)
        ·
          refine ⟨10926754908323252108753377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14569006544431002811671169 10926754908323252108753377)
          ·
            refine ⟨8195066181242439081565033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10926754908323252108753377 8195066181242439081565033)
            ·
              refine ⟨6146299635931829311173775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8195066181242439081565033 6146299635931829311173775)
              ·
                refine ⟨9219449453897743966760663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146299635931829311173775 9219449453897743966760663)
                ·
                  refine ⟨13829174180846615950140995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9219449453897743966760663 13829174180846615950140995)
                  ·
                    refine ⟨20743761271269923925211493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13829174180846615950140995 20743761271269923925211493)
                    ·
                      refine ⟨3889455238363110735977155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20743761271269923925211493 3889455238363110735977155)
                      ·
                        rfl

theorem cell23_7574687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7574687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574687 prefixEnd_7574687 := by exact prefixLift 7574687
  have htrace : WordTrace (prefixWord ++ tailWord_7574687) baseStart_7574687 baseEnd_7574687 := by
    simpa [prefixWord, tailWord_7574687, baseEnd_7574687] using wordTrace_append hprefix tailTrace_7574687
  have hstable : (prefixWord ++ tailWord_7574687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574687).length < 2 ^ (prefixWord ++ tailWord_7574687).sum := by decide
  have hdescent : baseEnd_7574687 < baseStart_7574687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574720 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 3]
def baseStart_7574720 : Nat := 118140960795 + 7574720 * 2 ^ 59
def prefixEnd_7574720 : Nat := 4983230072969 + 3 ^ 40 * 7574720 * 2
def baseEnd_7574720 : Nat := 3889472183224709106864503

theorem tailTrace_7574720 : CollatzResearch.WordTrace tailWord_7574720 prefixEnd_7574720 3889472183224709106864503 := by
  unfold tailWord_7574720
  simp only [CollatzResearch.WordTrace]
  refine ⟨138136367559045287013820807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184181823412060382685094409 138136367559045287013820807)
  ·
    refine ⟨207204551338567930520731211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138136367559045287013820807 207204551338567930520731211)
    ·
      refine ⟨310806827007851895781096817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207204551338567930520731211 310806827007851895781096817)
      ·
        refine ⟨233105120255888921835822613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310806827007851895781096817 233105120255888921835822613)
        ·
          refine ⟨10926802511994793211054185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 233105120255888921835822613 10926802511994793211054185)
          ·
            refine ⟨8195101883996094908290639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10926802511994793211054185 8195101883996094908290639)
            ·
              refine ⟨12292652825994142362435959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195101883996094908290639 12292652825994142362435959)
              ·
                refine ⟨18438979238991213543653939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12292652825994142362435959 18438979238991213543653939)
                ·
                  refine ⟨27658468858486820315480909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18438979238991213543653939 27658468858486820315480909)
                  ·
                    refine ⟨10371925821932557618305341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27658468858486820315480909 10371925821932557618305341)
                    ·
                      refine ⟨3889472183224709106864503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371925821932557618305341 3889472183224709106864503)
                      ·
                        rfl

theorem cell23_7574720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_7574720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574720 prefixEnd_7574720 := by exact prefixLift 7574720
  have htrace : WordTrace (prefixWord ++ tailWord_7574720) baseStart_7574720 baseEnd_7574720 := by
    simpa [prefixWord, tailWord_7574720, baseEnd_7574720] using wordTrace_append hprefix tailTrace_7574720
  have hstable : (prefixWord ++ tailWord_7574720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574720).length < 2 ^ (prefixWord ++ tailWord_7574720).sum := by decide
  have hdescent : baseEnd_7574720 < baseStart_7574720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574730 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_7574730 : Nat := 118140960795 + 7574730 * 2 ^ 59
def prefixEnd_7574730 : Nat := 4983230072969 + 3 ^ 40 * 7574730 * 2
def baseEnd_7574730 : Nat := 3889477318031254067739457

theorem tailTrace_7574730 : CollatzResearch.WordTrace tailWord_7574730 prefixEnd_7574730 3889477318031254067739457 := by
  unfold tailWord_7574730
  simp only [CollatzResearch.WordTrace]
  refine ⟨69068274962013586433876411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184182066565369563823670429 69068274962013586433876411)
  ·
    refine ⟨103602412443020379650814617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69068274962013586433876411 103602412443020379650814617)
    ·
      refine ⟨77701809332265284738110963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103602412443020379650814617 77701809332265284738110963)
      ·
        refine ⟨116552713998397927107166445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77701809332265284738110963 116552713998397927107166445)
        ·
          refine ⟨43707267749399222665187417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116552713998397927107166445 43707267749399222665187417)
          ·
            refine ⟨32780450812049416998890563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43707267749399222665187417 32780450812049416998890563)
            ·
              refine ⟨49170676218074125498335845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32780450812049416998890563 49170676218074125498335845)
              ·
                refine ⟨9219501790888898530937971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49170676218074125498335845 9219501790888898530937971)
                ·
                  refine ⟨13829252686333347796406957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9219501790888898530937971 13829252686333347796406957)
                  ·
                    refine ⟨5185969757375005423652609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13829252686333347796406957 5185969757375005423652609)
                    ·
                      refine ⟨3889477318031254067739457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185969757375005423652609 3889477318031254067739457)
                      ·
                        rfl

theorem cell23_7574730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_7574730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574730 prefixEnd_7574730 := by exact prefixLift 7574730
  have htrace : WordTrace (prefixWord ++ tailWord_7574730) baseStart_7574730 baseEnd_7574730 := by
    simpa [prefixWord, tailWord_7574730, baseEnd_7574730] using wordTrace_append hprefix tailTrace_7574730
  have hstable : (prefixWord ++ tailWord_7574730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574730).length < 2 ^ (prefixWord ++ tailWord_7574730).sum := by decide
  have hdescent : baseEnd_7574730 < baseStart_7574730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574743 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 1, 4, 2]
def baseStart_7574743 : Nat := 118140960795 + 7574743 * 2 ^ 59
def prefixEnd_7574743 : Nat := 4983230072969 + 3 ^ 40 * 7574743 * 2
def baseEnd_7574743 : Nat := 3889483993279762516876897

theorem tailTrace_7574743 : CollatzResearch.WordTrace tailWord_7574743 prefixEnd_7574743 3889483993279762516876897 := by
  unfold tailWord_7574743
  simp only [CollatzResearch.WordTrace]
  refine ⟨276273573997007248955728883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184182382664671499303819255 276273573997007248955728883)
  ·
    refine ⟨414410360995510873433593325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276273573997007248955728883 414410360995510873433593325)
    ·
      refine ⟨155403885373316577537597497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414410360995510873433593325 155403885373316577537597497)
      ·
        refine ⟨116552914029987433153198123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155403885373316577537597497 116552914029987433153198123)
        ·
          refine ⟨174829371044981149729797185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116552914029987433153198123 174829371044981149729797185)
          ·
            refine ⟨131122028283735862297347889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174829371044981149729797185 131122028283735862297347889)
            ·
              refine ⟨98341521212801896723010917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131122028283735862297347889 98341521212801896723010917)
              ·
                refine ⟨18439035227400355635564547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98341521212801896723010917 18439035227400355635564547)
                ·
                  refine ⟨27658552841100533453346821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18439035227400355635564547 27658552841100533453346821)
                  ·
                    refine ⟨5185978657706350022502529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27658552841100533453346821 5185978657706350022502529)
                    ·
                      refine ⟨3889483993279762516876897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185978657706350022502529 3889483993279762516876897)
                      ·
                        rfl

theorem cell23_7574743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_7574743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574743 prefixEnd_7574743 := by exact prefixLift 7574743
  have htrace : WordTrace (prefixWord ++ tailWord_7574743) baseStart_7574743 baseEnd_7574743 := by
    simpa [prefixWord, tailWord_7574743, baseEnd_7574743] using wordTrace_append hprefix tailTrace_7574743
  have hstable : (prefixWord ++ tailWord_7574743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574743).length < 2 ^ (prefixWord ++ tailWord_7574743).sum := by decide
  have hdescent : baseEnd_7574743 < baseStart_7574743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574746 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_7574746 : Nat := 118140960795 + 7574746 * 2 ^ 59
def prefixEnd_7574746 : Nat := 4983230072969 + 3 ^ 40 * 7574746 * 2
def baseEnd_7574746 : Nat := 3889485533721726005139383

theorem tailTrace_7574746 : CollatzResearch.WordTrace tailWord_7574746 prefixEnd_7574746 3889485533721726005139383 := by
  unfold tailWord_7574746
  simp only [CollatzResearch.WordTrace]
  refine ⟨69068420853999095117022023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184182455610664253645392061 69068420853999095117022023)
  ·
    refine ⟨103602631280998642675533035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69068420853999095117022023 103602631280998642675533035)
    ·
      refine ⟨155403946921497964013299553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103602631280998642675533035 155403946921497964013299553)
      ·
        refine ⟨116552960191123473009974665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155403946921497964013299553 116552960191123473009974665)
        ·
          refine ⟨87414720143342604757480999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116552960191123473009974665 87414720143342604757480999)
          ·
            refine ⟨131122080215013907136221499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87414720143342604757480999 131122080215013907136221499)
            ·
              refine ⟨196683120322520860704332249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131122080215013907136221499 196683120322520860704332249)
              ·
                refine ⟨147512340241890645528249187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196683120322520860704332249 147512340241890645528249187)
                ·
                  refine ⟨221268510362835968292373781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147512340241890645528249187 221268510362835968292373781)
                  ·
                    refine ⟨10371961423257936013705021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 221268510362835968292373781 10371961423257936013705021)
                    ·
                      refine ⟨3889485533721726005139383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10371961423257936013705021 3889485533721726005139383)
                      ·
                        rfl

theorem cell23_7574746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_7574746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574746 prefixEnd_7574746 := by exact prefixLift 7574746
  have htrace : WordTrace (prefixWord ++ tailWord_7574746) baseStart_7574746 baseEnd_7574746 := by
    simpa [prefixWord, tailWord_7574746, baseEnd_7574746] using wordTrace_append hprefix tailTrace_7574746
  have hstable : (prefixWord ++ tailWord_7574746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574746).length < 2 ^ (prefixWord ++ tailWord_7574746).sum := by decide
  have hdescent : baseEnd_7574746 < baseStart_7574746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574756 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_7574756 : Nat := 118140960795 + 7574756 * 2 ^ 59
def prefixEnd_7574756 : Nat := 4983230072969 + 3 ^ 40 * 7574756 * 2
def baseEnd_7574756 : Nat := 3889490668528270966014337

theorem tailTrace_7574756 : CollatzResearch.WordTrace tailWord_7574756 prefixEnd_7574756 3889490668528270966014337 := by
  unfold tailWord_7574756
  simp only [CollatzResearch.WordTrace]
  refine ⟨138137024072980076087976061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184182698763973434783968081 138137024072980076087976061)
  ·
    refine ⟨51801384027367528532991023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138137024072980076087976061 51801384027367528532991023)
    ·
      refine ⟨77702076041051292799486535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51801384027367528532991023 77702076041051292799486535)
      ·
        refine ⟨116553114061576939199229803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77702076041051292799486535 116553114061576939199229803)
        ·
          refine ⟨174829671092365408798844705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116553114061576939199229803 174829671092365408798844705)
          ·
            refine ⟨131122253319274056599133529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174829671092365408798844705 131122253319274056599133529)
            ·
              refine ⟨98341689989455542449350147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131122253319274056599133529 98341689989455542449350147)
              ·
                refine ⟨147512534984183313674025221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98341689989455542449350147 147512534984183313674025221)
                ·
                  refine ⟨27658600309534371313879729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147512534984183313674025221 27658600309534371313879729)
                  ·
                    refine ⟨20743950232150778485409797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27658600309534371313879729 20743950232150778485409797)
                    ·
                      refine ⟨3889490668528270966014337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20743950232150778485409797 3889490668528270966014337)
                      ·
                        rfl

theorem cell23_7574756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_7574756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574756 prefixEnd_7574756 := by exact prefixLift 7574756
  have htrace : WordTrace (prefixWord ++ tailWord_7574756) baseStart_7574756 baseEnd_7574756 := by
    simpa [prefixWord, tailWord_7574756, baseEnd_7574756] using wordTrace_append hprefix tailTrace_7574756
  have hstable : (prefixWord ++ tailWord_7574756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574756).length < 2 ^ (prefixWord ++ tailWord_7574756).sum := by decide
  have hdescent : baseEnd_7574756 < baseStart_7574756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574760 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_7574760 : Nat := 118140960795 + 7574760 * 2 ^ 59
def prefixEnd_7574760 : Nat := 4983230072969 + 3 ^ 40 * 7574760 * 2
def baseEnd_7574760 : Nat := 3889492722450888950364319

theorem tailTrace_7574760 : CollatzResearch.WordTrace tailWord_7574760 prefixEnd_7574760 3889492722450888950364319 := by
  unfold tailWord_7574760
  simp only [CollatzResearch.WordTrace]
  refine ⟨138137097018972830429548867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184182796025297107239398489 138137097018972830429548867)
  ·
    refine ⟨207205645528459245644323301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138137097018972830429548867 207205645528459245644323301)
    ·
      refine ⟨38851058536586108558310619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207205645528459245644323301 38851058536586108558310619)
      ·
        refine ⟨58276587804879162837465929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38851058536586108558310619 58276587804879162837465929)
        ·
          refine ⟨43707440853659372128099447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58276587804879162837465929 43707440853659372128099447)
          ·
            refine ⟨65561161280489058192149171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43707440853659372128099447 65561161280489058192149171)
            ·
              refine ⟨98341741920733587288223757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65561161280489058192149171 98341741920733587288223757)
              ·
                refine ⟨36878153220275095233083909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98341741920733587288223757 36878153220275095233083909)
                ·
                  refine ⟨6914653728801580356203233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36878153220275095233083909 6914653728801580356203233)
                  ·
                    refine ⟨5185990296601185267152425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6914653728801580356203233 5185990296601185267152425)
                    ·
                      refine ⟨3889492722450888950364319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5185990296601185267152425 3889492722450888950364319)
                      ·
                        rfl

theorem cell23_7574760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_7574760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574760 prefixEnd_7574760 := by exact prefixLift 7574760
  have htrace : WordTrace (prefixWord ++ tailWord_7574760) baseStart_7574760 baseEnd_7574760 := by
    simpa [prefixWord, tailWord_7574760, baseEnd_7574760] using wordTrace_append hprefix tailTrace_7574760
  have hstable : (prefixWord ++ tailWord_7574760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574760).length < 2 ^ (prefixWord ++ tailWord_7574760).sum := by decide
  have hdescent : baseEnd_7574760 < baseStart_7574760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574856 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 8]
def baseStart_7574856 : Nat := 118140960795 + 7574856 * 2 ^ 59
def prefixEnd_7574856 : Nat := 4983230072969 + 3 ^ 40 * 7574856 * 2
def baseEnd_7574856 : Nat := 432171335177080063862653

theorem tailTrace_7574856 : CollatzResearch.WordTrace tailWord_7574856 prefixEnd_7574856 432171335177080063862653 := by
  unfold tailWord_7574856
  simp only [CollatzResearch.WordTrace]
  refine ⟨138138847722798934627296211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184185130297065246169728281 138138847722798934627296211)
  ·
    refine ⟨207208271584198401940944317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138138847722798934627296211 207208271584198401940944317)
    ·
      refine ⟨77703101844074400727854119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207208271584198401940944317 77703101844074400727854119)
      ·
        refine ⟨116554652766111601091781179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77703101844074400727854119 116554652766111601091781179)
        ·
          refine ⟨174831979149167401637671769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116554652766111601091781179 174831979149167401637671769)
          ·
            refine ⟨131123984361875551228253827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174831979149167401637671769 131123984361875551228253827)
            ·
              refine ⟨196685976542813326842380741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131123984361875551228253827 196685976542813326842380741)
              ·
                refine ⟨36878620601777498782946389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196685976542813326842380741 36878620601777498782946389)
                ·
                  refine ⟨432171335177080063862653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36878620601777498782946389 432171335177080063862653)
                  ·
                    rfl

theorem cell23_7574856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 8].length) (baseStart_7574856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574856 prefixEnd_7574856 := by exact prefixLift 7574856
  have htrace : WordTrace (prefixWord ++ tailWord_7574856) baseStart_7574856 baseEnd_7574856 := by
    simpa [prefixWord, tailWord_7574856, baseEnd_7574856] using wordTrace_append hprefix tailTrace_7574856
  have hstable : (prefixWord ++ tailWord_7574856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574856).length < 2 ^ (prefixWord ++ tailWord_7574856).sum := by decide
  have hdescent : baseEnd_7574856 < baseStart_7574856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574873 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 6]
def baseStart_7574873 : Nat := 118140960795 + 7574873 * 2 ^ 59
def prefixEnd_7574873 : Nat := 4983230072969 + 3 ^ 40 * 7574873 * 2
def baseEnd_7574873 : Nat := 432172305084983000916811

theorem tailTrace_7574873 : CollatzResearch.WordTrace tailWord_7574873 prefixEnd_7574873 432172305084983000916811 := by
  unfold tailWord_7574873
  simp only [CollatzResearch.WordTrace]
  refine ⟨276278315486536281157961273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184185543657690854105307515 276278315486536281157961273)
  ·
    refine ⟨207208736614902210868470955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276278315486536281157961273 207208736614902210868470955)
    ·
      refine ⟨310813104922353316302706433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207208736614902210868470955 310813104922353316302706433)
      ·
        refine ⟨233109828691764987227029825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310813104922353316302706433 233109828691764987227029825)
        ·
          refine ⟨174832371518823740420272369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233109828691764987227029825 174832371518823740420272369)
          ·
            refine ⟨131124278639117805315204277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174832371518823740420272369 131124278639117805315204277)
            ·
              refine ⟨12292901122417294248300401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131124278639117805315204277 12292901122417294248300401)
              ·
                refine ⟨9219675841812970686225301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12292901122417294248300401 9219675841812970686225301)
                ·
                  refine ⟨432172305084983000916811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9219675841812970686225301 432172305084983000916811)
                  ·
                    rfl

theorem cell23_7574873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 6].length) (baseStart_7574873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574873 prefixEnd_7574873 := by exact prefixLift 7574873
  have htrace : WordTrace (prefixWord ++ tailWord_7574873) baseStart_7574873 baseEnd_7574873 := by
    simpa [prefixWord, tailWord_7574873, baseEnd_7574873] using wordTrace_append hprefix tailTrace_7574873
  have hstable : (prefixWord ++ tailWord_7574873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574873).length < 2 ^ (prefixWord ++ tailWord_7574873).sum := by decide
  have hdescent : baseEnd_7574873 < baseStart_7574873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574920 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 1, 5]
def baseStart_7574920 : Nat := 118140960795 + 7574920 * 2 ^ 59
def prefixEnd_7574920 : Nat := 4983230072969 + 3 ^ 40 * 7574920 * 2
def baseEnd_7574920 : Nat := 1296524959785202774787861

theorem tailTrace_7574920 : CollatzResearch.WordTrace tailWord_7574920 prefixEnd_7574920 1296524959785202774787861 := by
  unfold tailWord_7574920
  simp only [CollatzResearch.WordTrace]
  refine ⟨138140014858683004092461107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184186686478244005456614809 138140014858683004092461107)
  ·
    refine ⟨207210022288024506138691661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138140014858683004092461107 207210022288024506138691661)
    ·
      refine ⟨77703758358009189802009373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207210022288024506138691661 77703758358009189802009373)
      ·
        refine ⟨29138909384253446175753515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77703758358009189802009373 29138909384253446175753515)
        ·
          refine ⟨43708364076380169263630273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29138909384253446175753515 43708364076380169263630273)
          ·
            refine ⟨32781273057285126947722705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43708364076380169263630273 32781273057285126947722705)
            ·
              refine ⟨24585954792963845210792029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32781273057285126947722705 24585954792963845210792029)
              ·
                refine ⟨9219733047361441954047011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24585954792963845210792029 9219733047361441954047011)
                ·
                  refine ⟨13829599571042162931070517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9219733047361441954047011 13829599571042162931070517)
                  ·
                    refine ⟨1296524959785202774787861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13829599571042162931070517 1296524959785202774787861)
                    ·
                      rfl

theorem cell23_7574920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_7574920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574920 prefixEnd_7574920 := by exact prefixLift 7574920
  have htrace : WordTrace (prefixWord ++ tailWord_7574920) baseStart_7574920 baseEnd_7574920 := by
    simpa [prefixWord, tailWord_7574920, baseEnd_7574920] using wordTrace_append hprefix tailTrace_7574920
  have hstable : (prefixWord ++ tailWord_7574920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574920).length < 2 ^ (prefixWord ++ tailWord_7574920).sum := by decide
  have hdescent : baseEnd_7574920 < baseStart_7574920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574957 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7574957 : Nat := 118140960795 + 7574957 * 2 ^ 59
def prefixEnd_7574957 : Nat := 4983230072969 + 3 ^ 40 * 7574957 * 2
def baseEnd_7574957 : Nat := 3889593878139824679600913

theorem tailTrace_7574957 : CollatzResearch.WordTrace tailWord_7574957 prefixEnd_7574957 3889593878139824679600913 := by
  unfold tailWord_7574957
  simp only [CollatzResearch.WordTrace]
  refine ⟨276281379218231963504019125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184187586145487975669346083 276281379218231963504019125)
  ·
    refine ⟨25901379301709246578501793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276281379218231963504019125 25901379301709246578501793)
    ·
      refine ⟨19426034476281934933876345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25901379301709246578501793 19426034476281934933876345)
      ·
        refine ⟨14569525857211451200407259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19426034476281934933876345 14569525857211451200407259)
        ·
          refine ⟨21854288785817176800610889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14569525857211451200407259 21854288785817176800610889)
          ·
            refine ⟨16390716589362882600458167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21854288785817176800610889 16390716589362882600458167)
            ·
              refine ⟨24586074884044323900687251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16390716589362882600458167 24586074884044323900687251)
              ·
                refine ⟨36879112326066485851030877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24586074884044323900687251 36879112326066485851030877)
                ·
                  refine ⟨13829667122274932194136579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36879112326066485851030877 13829667122274932194136579)
                  ·
                    refine ⟨20744500683412398291204869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13829667122274932194136579 20744500683412398291204869)
                    ·
                      refine ⟨3889593878139824679600913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20744500683412398291204869 3889593878139824679600913)
                      ·
                        rfl

theorem cell23_7574957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7574957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574957 prefixEnd_7574957 := by exact prefixLift 7574957
  have htrace : WordTrace (prefixWord ++ tailWord_7574957) baseStart_7574957 baseEnd_7574957 := by
    simpa [prefixWord, tailWord_7574957, baseEnd_7574957] using wordTrace_append hprefix tailTrace_7574957
  have hstable : (prefixWord ++ tailWord_7574957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574957).length < 2 ^ (prefixWord ++ tailWord_7574957).sum := by decide
  have hdescent : baseEnd_7574957 < baseStart_7574957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574960 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 3]
def baseStart_7574960 : Nat := 118140960795 + 7574960 * 2 ^ 59
def prefixEnd_7574960 : Nat := 4983230072969 + 3 ^ 40 * 7574960 * 2
def baseEnd_7574960 : Nat := 3889595418581788167863399

theorem tailTrace_7574960 : CollatzResearch.WordTrace tailWord_7574960 prefixEnd_7574960 3889595418581788167863399 := by
  unfold tailWord_7574960
  simp only [CollatzResearch.WordTrace]
  refine ⟨138140744318610547508189167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184187659091480730010918889 138140744318610547508189167)
  ·
    refine ⟨207211116477915821262283751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138140744318610547508189167 207211116477915821262283751)
    ·
      refine ⟨310816674716873731893425627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207211116477915821262283751 310816674716873731893425627)
      ·
        refine ⟨466225012075310597840138441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310816674716873731893425627 466225012075310597840138441)
        ·
          refine ⟨349668759056482948380103831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466225012075310597840138441 349668759056482948380103831)
          ·
            refine ⟨524503138584724422570155747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349668759056482948380103831 524503138584724422570155747)
            ·
              refine ⟨786754707877086633855233621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524503138584724422570155747 786754707877086633855233621)
              ·
                refine ⟨9219781732934608990491019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 786754707877086633855233621 9219781732934608990491019)
                ·
                  refine ⟨13829672599401913485736529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9219781732934608990491019 13829672599401913485736529)
                  ·
                    refine ⟨10372254449551435114302397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13829672599401913485736529 10372254449551435114302397)
                    ·
                      refine ⟨3889595418581788167863399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10372254449551435114302397 3889595418581788167863399)
                      ·
                        rfl

theorem cell23_7574960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 3].length) (baseStart_7574960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574960 prefixEnd_7574960 := by exact prefixLift 7574960
  have htrace : WordTrace (prefixWord ++ tailWord_7574960) baseStart_7574960 baseEnd_7574960 := by
    simpa [prefixWord, tailWord_7574960, baseEnd_7574960] using wordTrace_append hprefix tailTrace_7574960
  have hstable : (prefixWord ++ tailWord_7574960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574960).length < 2 ^ (prefixWord ++ tailWord_7574960).sum := by decide
  have hdescent : baseEnd_7574960 < baseStart_7574960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7574991 : List Nat := [1, 1, 2, 1, 1, 4, 6, 2, 1, 2, 2]
def baseStart_7574991 : Nat := 118140960795 + 7574991 * 2 ^ 59
def prefixEnd_7574991 : Nat := 4983230072969 + 3 ^ 40 * 7574991 * 2
def baseEnd_7574991 : Nat := 3889611336482077546575757

theorem tailTrace_7574991 : CollatzResearch.WordTrace tailWord_7574991 prefixEnd_7574991 3889611336482077546575757 := by
  unfold tailWord_7574991
  simp only [CollatzResearch.WordTrace]
  refine ⟨276282619300108787310756827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184188412866739191540504551 276282619300108787310756827)
  ·
    refine ⟨414423928950163180966135241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276282619300108787310756827 414423928950163180966135241)
    ·
      refine ⟨310817946712622385724601431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414423928950163180966135241 310817946712622385724601431)
      ·
        refine ⟨466226920068933578586902147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310817946712622385724601431 466226920068933578586902147)
        ·
          refine ⟨699340380103400367880353221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466226920068933578586902147 699340380103400367880353221)
          ·
            refine ⟨131126321269387568977566229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 699340380103400367880353221 131126321269387568977566229)
            ·
              refine ⟨6146546309502542295823417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131126321269387568977566229 6146546309502542295823417)
              ·
                refine ⟨4609909732126906721867563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6146546309502542295823417 4609909732126906721867563)
                ·
                  refine ⟨6914864598190360082801345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609909732126906721867563 6914864598190360082801345)
                  ·
                    refine ⟨5186148448642770062101009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6914864598190360082801345 5186148448642770062101009)
                    ·
                      refine ⟨3889611336482077546575757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5186148448642770062101009 3889611336482077546575757)
                      ·
                        rfl

theorem cell23_7574991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 2, 2].length) (baseStart_7574991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7574991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7574991 prefixEnd_7574991 := by exact prefixLift 7574991
  have htrace : WordTrace (prefixWord ++ tailWord_7574991) baseStart_7574991 baseEnd_7574991 := by
    simpa [prefixWord, tailWord_7574991, baseEnd_7574991] using wordTrace_append hprefix tailTrace_7574991
  have hstable : (prefixWord ++ tailWord_7574991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7574991).length < 2 ^ (prefixWord ++ tailWord_7574991).sum := by decide
  have hdescent : baseEnd_7574991 < baseStart_7574991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7574991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575007 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 3]
def baseStart_7575007 : Nat := 118140960795 + 7575007 * 2 ^ 59
def prefixEnd_7575007 : Nat := 4983230072969 + 3 ^ 40 * 7575007 * 2
def baseEnd_7575007 : Nat := 3889619552172549483975683

theorem tailTrace_7575007 : CollatzResearch.WordTrace tailWord_7575007 prefixEnd_7575007 3889619552172549483975683 := by
  unfold tailWord_7575007
  simp only [CollatzResearch.WordTrace]
  refine ⟨276283202868050822043339275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184188801912033881362226183 276283202868050822043339275)
  ·
    refine ⟨414424804302076233065008913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276283202868050822043339275 414424804302076233065008913)
    ·
      refine ⟨310818603226557174798756685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414424804302076233065008913 310818603226557174798756685)
      ·
        refine ⟨116556976209958940549533757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310818603226557174798756685 116556976209958940549533757)
        ·
          refine ⟨43708866078734602706075159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116556976209958940549533757 43708866078734602706075159)
          ·
            refine ⟨65563299118101904059112739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43708866078734602706075159 65563299118101904059112739)
            ·
              refine ⟨98344948677152856088669109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65563299118101904059112739 98344948677152856088669109)
              ·
                refine ⟨9219838938483080258312729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98344948677152856088669109 9219838938483080258312729)
                ·
                  refine ⟨6914879203862310193734547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9219838938483080258312729 6914879203862310193734547)
                  ·
                    refine ⟨10372318805793465290601821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6914879203862310193734547 10372318805793465290601821)
                    ·
                      refine ⟨3889619552172549483975683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10372318805793465290601821 3889619552172549483975683)
                      ·
                        rfl

theorem cell23_7575007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_7575007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575007 prefixEnd_7575007 := by exact prefixLift 7575007
  have htrace : WordTrace (prefixWord ++ tailWord_7575007) baseStart_7575007 baseEnd_7575007 := by
    simpa [prefixWord, tailWord_7575007, baseEnd_7575007] using wordTrace_append hprefix tailTrace_7575007
  have hstable : (prefixWord ++ tailWord_7575007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575007).length < 2 ^ (prefixWord ++ tailWord_7575007).sum := by decide
  have hdescent : baseEnd_7575007 < baseStart_7575007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575033 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_7575033 : Nat := 118140960795 + 7575033 * 2 ^ 59
def prefixEnd_7575033 : Nat := 4983230072969 + 3 ^ 40 * 7575033 * 2
def baseEnd_7575033 : Nat := 3889632902669566382250563

theorem tailTrace_7575033 : CollatzResearch.WordTrace tailWord_7575033 prefixEnd_7575033 3889632902669566382250563 := by
  unfold tailWord_7575033
  simp only [CollatzResearch.WordTrace]
  refine ⟨276284151165956628483785753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184189434110637752322523835 276284151165956628483785753)
  ·
    refine ⟨207213113374467471362839315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276284151165956628483785753 207213113374467471362839315)
    ·
      refine ⟨310819670061701207044258973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207213113374467471362839315 310819670061701207044258973)
      ·
        refine ⟨116557376273137952641597115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310819670061701207044258973 116557376273137952641597115)
        ·
          refine ⟨174836064409706928962395673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116557376273137952641597115 174836064409706928962395673)
          ·
            refine ⟨131127048307280196721796755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174836064409706928962395673 131127048307280196721796755)
            ·
              refine ⟨196690572460920295082695133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131127048307280196721796755 196690572460920295082695133)
              ·
                refine ⟨73758964672845110656010675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196690572460920295082695133 73758964672845110656010675)
                ·
                  refine ⟨110638447009267665984016013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73758964672845110656010675 110638447009267665984016013)
                  ·
                    refine ⟨41489417628475374744006005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110638447009267665984016013 41489417628475374744006005)
                    ·
                      refine ⟨3889632902669566382250563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41489417628475374744006005 3889632902669566382250563)
                      ·
                        rfl

theorem cell23_7575033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_7575033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575033 prefixEnd_7575033 := by exact prefixLift 7575033
  have htrace : WordTrace (prefixWord ++ tailWord_7575033) baseStart_7575033 baseEnd_7575033 := by
    simpa [prefixWord, tailWord_7575033, baseEnd_7575033] using wordTrace_append hprefix tailTrace_7575033
  have hstable : (prefixWord ++ tailWord_7575033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575033).length < 2 ^ (prefixWord ++ tailWord_7575033).sum := by decide
  have hdescent : baseEnd_7575033 < baseStart_7575033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575041 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_7575041 : Nat := 118140960795 + 7575041 * 2 ^ 59
def prefixEnd_7575041 : Nat := 4983230072969 + 3 ^ 40 * 7575041 * 2
def baseEnd_7575041 : Nat := 3889637010514802350950527

theorem tailTrace_7575041 : CollatzResearch.WordTrace tailWord_7575041 prefixEnd_7575041 3889637010514802350950527 := by
  unfold tailWord_7575041
  simp only [CollatzResearch.WordTrace]
  refine ⟨276284442949927645850076977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184189628633285097233384651 276284442949927645850076977)
  ·
    refine ⟨207213332212445734387557733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276284442949927645850076977 207213332212445734387557733)
    ·
      refine ⟨38852499789833575197667075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207213332212445734387557733 38852499789833575197667075)
      ·
        refine ⟨58278749684750362796500613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38852499789833575197667075 58278749684750362796500613)
        ·
          refine ⟨10927265565890693024343865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58278749684750362796500613 10927265565890693024343865)
          ·
            refine ⟨8195449174418019768257899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10927265565890693024343865 8195449174418019768257899)
            ·
              refine ⟨12293173761627029652386849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195449174418019768257899 12293173761627029652386849)
              ·
                refine ⟨9219880321220272239290137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12293173761627029652386849 9219880321220272239290137)
                ·
                  refine ⟨6914910240915204179467603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9219880321220272239290137 6914910240915204179467603)
                  ·
                    refine ⟨10372365361372806269201405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6914910240915204179467603 10372365361372806269201405)
                    ·
                      refine ⟨3889637010514802350950527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10372365361372806269201405 3889637010514802350950527)
                      ·
                        rfl

theorem cell23_7575041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_7575041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575041 prefixEnd_7575041 := by exact prefixLift 7575041
  have htrace : WordTrace (prefixWord ++ tailWord_7575041) baseStart_7575041 baseEnd_7575041 := by
    simpa [prefixWord, tailWord_7575041, baseEnd_7575041] using wordTrace_append hprefix tailTrace_7575041
  have hstable : (prefixWord ++ tailWord_7575041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575041).length < 2 ^ (prefixWord ++ tailWord_7575041).sum := by decide
  have hdescent : baseEnd_7575041 < baseStart_7575041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575120 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_7575120 : Nat := 118140960795 + 7575120 * 2 ^ 59
def prefixEnd_7575120 : Nat := 4983230072969 + 3 ^ 40 * 7575120 * 2
def baseEnd_7575120 : Nat := 3889677575486507541862663

theorem tailTrace_7575120 : CollatzResearch.WordTrace tailWord_7575120 prefixEnd_7575120 3889677575486507541862663 := by
  unfold tailWord_7575120
  simp only [CollatzResearch.WordTrace]
  refine ⟨138143662158320721171101407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184191549544427628228135209 138143662158320721171101407)
  ·
    refine ⟨207215493237481081756652111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138143662158320721171101407 207215493237481081756652111)
    ·
      refine ⟨310823239856221622634978167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207215493237481081756652111 310823239856221622634978167)
      ·
        refine ⟨466234859784332433952467251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310823239856221622634978167 466234859784332433952467251)
        ·
          refine ⟨699352289676498650928700877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466234859784332433952467251 699352289676498650928700877)
          ·
            refine ⟨262257108628686994098262829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 699352289676498650928700877 262257108628686994098262829)
            ·
              refine ⟨98346415735757622786848561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262257108628686994098262829 98346415735757622786848561)
              ·
                refine ⟨73759811801818217090136421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98346415735757622786848561 73759811801818217090136421)
                ·
                  refine ⟨13829964712840915704400579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73759811801818217090136421 13829964712840915704400579)
                  ·
                    refine ⟨20744947069261373556600869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13829964712840915704400579 20744947069261373556600869)
                    ·
                      refine ⟨3889677575486507541862663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20744947069261373556600869 3889677575486507541862663)
                      ·
                        rfl

theorem cell23_7575120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_7575120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575120 prefixEnd_7575120 := by exact prefixLift 7575120
  have htrace : WordTrace (prefixWord ++ tailWord_7575120) baseStart_7575120 baseEnd_7575120 := by
    simpa [prefixWord, tailWord_7575120, baseEnd_7575120] using wordTrace_append hprefix tailTrace_7575120
  have hstable : (prefixWord ++ tailWord_7575120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575120).length < 2 ^ (prefixWord ++ tailWord_7575120).sum := by decide
  have hdescent : baseEnd_7575120 < baseStart_7575120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575137 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_7575137 : Nat := 118140960795 + 7575137 * 2 ^ 59
def prefixEnd_7575137 : Nat := 4983230072969 + 3 ^ 40 * 7575137 * 2
def baseEnd_7575137 : Nat := 3889686304657633975350085

theorem tailTrace_7575137 : CollatzResearch.WordTrace tailWord_7575137 prefixEnd_7575137 3889686304657633975350085 := by
  unfold tailWord_7575137
  simp only [CollatzResearch.WordTrace]
  refine ⟨276287944357579854245571665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184191962905053236163714443 276287944357579854245571665)
  ·
    refine ⟨207215958268184890684178749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276287944357579854245571665 207215958268184890684178749)
    ·
      refine ⟨77705984350569334006567031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207215958268184890684178749 77705984350569334006567031)
      ·
        refine ⟨116558976525854001009850547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77705984350569334006567031 116558976525854001009850547)
        ·
          refine ⟨174838464788781001514775821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116558976525854001009850547 174838464788781001514775821)
          ·
            refine ⟨65564424295792875568040933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174838464788781001514775821 65564424295792875568040933)
            ·
              refine ⟨12293329555461164169007675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65564424295792875568040933 12293329555461164169007675)
              ·
                refine ⟨18439994333191746253511513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12293329555461164169007675 18439994333191746253511513)
                ·
                  refine ⟨13829995749893809690133635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18439994333191746253511513 13829995749893809690133635)
                  ·
                    refine ⟨20744993624840714535200453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13829995749893809690133635 20744993624840714535200453)
                    ·
                      refine ⟨3889686304657633975350085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20744993624840714535200453 3889686304657633975350085)
                      ·
                        rfl

theorem cell23_7575137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_7575137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575137 prefixEnd_7575137 := by exact prefixLift 7575137
  have htrace : WordTrace (prefixWord ++ tailWord_7575137) baseStart_7575137 baseEnd_7575137 := by
    simpa [prefixWord, tailWord_7575137, baseEnd_7575137] using wordTrace_append hprefix tailTrace_7575137
  have hstable : (prefixWord ++ tailWord_7575137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575137).length < 2 ^ (prefixWord ++ tailWord_7575137).sum := by decide
  have hdescent : baseEnd_7575137 < baseStart_7575137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575188 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_7575188 : Nat := 118140960795 + 7575188 * 2 ^ 59
def prefixEnd_7575188 : Nat := 4983230072969 + 3 ^ 40 * 7575188 * 2
def baseEnd_7575188 : Nat := 3889712492171013275812351

theorem tailTrace_7575188 : CollatzResearch.WordTrace tailWord_7575188 prefixEnd_7575188 3889712492171013275812351 := by
  unfold tailWord_7575188
  simp only [CollatzResearch.WordTrace]
  refine ⟨138144902240197544977839109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184193202986930059970452145 138144902240197544977839109)
  ·
    refine ⟨25902169170037039683344833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138144902240197544977839109 25902169170037039683344833)
    ·
      refine ⟨19426626877527779762508625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25902169170037039683344833 19426626877527779762508625)
      ·
        refine ⟨14569970158145834821881469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19426626877527779762508625 14569970158145834821881469)
        ·
          refine ⟨5463738809304688058205551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14569970158145834821881469 5463738809304688058205551)
          ·
            refine ⟨8195608213957032087308327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463738809304688058205551 8195608213957032087308327)
            ·
              refine ⟨12293412320935548130962491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195608213957032087308327 12293412320935548130962491)
              ·
                refine ⟨18440118481403322196443737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12293412320935548130962491 18440118481403322196443737)
                ·
                  refine ⟨13830088861052491647332803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18440118481403322196443737 13830088861052491647332803)
                  ·
                    refine ⟨20745133291578737470999205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13830088861052491647332803 20745133291578737470999205)
                    ·
                      refine ⟨3889712492171013275812351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20745133291578737470999205 3889712492171013275812351)
                      ·
                        rfl

theorem cell23_7575188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_7575188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575188 prefixEnd_7575188 := by exact prefixLift 7575188
  have htrace : WordTrace (prefixWord ++ tailWord_7575188) baseStart_7575188 baseEnd_7575188 := by
    simpa [prefixWord, tailWord_7575188, baseEnd_7575188] using wordTrace_append hprefix tailTrace_7575188
  have hstable : (prefixWord ++ tailWord_7575188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575188).length < 2 ^ (prefixWord ++ tailWord_7575188).sum := by decide
  have hdescent : baseEnd_7575188 < baseStart_7575188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575198 : List Nat := [4, 3, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_7575198 : Nat := 118140960795 + 7575198 * 2 ^ 59
def prefixEnd_7575198 : Nat := 4983230072969 + 3 ^ 40 * 7575198 * 2
def baseEnd_7575198 : Nat := 1296572542325852745562435

theorem tailTrace_7575198 : CollatzResearch.WordTrace tailWord_7575198 prefixEnd_7575198 1296572542325852745562435 := by
  unfold tailWord_7575198
  simp only [CollatzResearch.WordTrace]
  refine ⟨34536271151294857707942781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184193446140239241109028165 34536271151294857707942781)
  ·
    refine ⟨12951101681735571640478543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34536271151294857707942781 12951101681735571640478543)
    ·
      refine ⟨19426652522603357460717815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12951101681735571640478543 19426652522603357460717815)
      ·
        refine ⟨29139978783905036191076723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19426652522603357460717815 29139978783905036191076723)
        ·
          refine ⟨43709968175857554286615085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29139978783905036191076723 43709968175857554286615085)
          ·
            refine ⟨16391238065946582857480657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43709968175857554286615085 16391238065946582857480657)
            ·
              refine ⟨12293428549459937143110493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16391238065946582857480657 12293428549459937143110493)
              ·
                refine ⟨4610035706047476428666435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12293428549459937143110493 4610035706047476428666435)
                ·
                  refine ⟨6915053559071214642999653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610035706047476428666435 6915053559071214642999653)
                  ·
                    refine ⟨1296572542325852745562435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6915053559071214642999653 1296572542325852745562435)
                    ·
                      rfl

theorem cell23_7575198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_7575198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575198 prefixEnd_7575198 := by exact prefixLift 7575198
  have htrace : WordTrace (prefixWord ++ tailWord_7575198) baseStart_7575198 baseEnd_7575198 := by
    simpa [prefixWord, tailWord_7575198, baseEnd_7575198] using wordTrace_append hprefix tailTrace_7575198
  have hstable : (prefixWord ++ tailWord_7575198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575198).length < 2 ^ (prefixWord ++ tailWord_7575198).sum := by decide
  have hdescent : baseEnd_7575198 < baseStart_7575198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575247 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 3]
def baseStart_7575247 : Nat := 118140960795 + 7575247 * 2 ^ 59
def prefixEnd_7575247 : Nat := 4983230072969 + 3 ^ 40 * 7575247 * 2
def baseEnd_7575247 : Nat := 3889742787529628544974579

theorem tailTrace_7575247 : CollatzResearch.WordTrace tailWord_7575247 prefixEnd_7575247 3889742787529628544974579 := by
  unfold tailWord_7575247
  simp only [CollatzResearch.WordTrace]
  refine ⟨276291956387181343032075995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184194637591454228688050663 276291956387181343032075995)
  ·
    refine ⟨414437934580772014548113993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276291956387181343032075995 414437934580772014548113993)
    ·
      refine ⟨310828450935579010911085495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414437934580772014548113993 310828450935579010911085495)
      ·
        refine ⟨466242676403368516366628243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310828450935579010911085495 466242676403368516366628243)
        ·
          refine ⟨699364014605052774549942365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466242676403368516366628243 699364014605052774549942365)
          ·
            refine ⟨262261505476894790456228387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 699364014605052774549942365 262261505476894790456228387)
            ·
              refine ⟨393392258215342185684342581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262261505476894790456228387 393392258215342185684342581)
              ·
                refine ⟨36880524207688329907907117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 393392258215342185684342581 36880524207688329907907117)
                ·
                  refine ⟨13830196577883123715465169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36880524207688329907907117 13830196577883123715465169)
                  ·
                    refine ⟨10372647433412342786598877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13830196577883123715465169 10372647433412342786598877)
                    ·
                      refine ⟨3889742787529628544974579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10372647433412342786598877 3889742787529628544974579)
                      ·
                        rfl

theorem cell23_7575247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_7575247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575247 prefixEnd_7575247 := by exact prefixLift 7575247
  have htrace : WordTrace (prefixWord ++ tailWord_7575247) baseStart_7575247 baseEnd_7575247 := by
    simpa [prefixWord, tailWord_7575247, baseEnd_7575247] using wordTrace_append hprefix tailTrace_7575247
  have hstable : (prefixWord ++ tailWord_7575247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575247).length < 2 ^ (prefixWord ++ tailWord_7575247).sum := by decide
  have hdescent : baseEnd_7575247 < baseStart_7575247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575264 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 3]
def baseStart_7575264 : Nat := 118140960795 + 7575264 * 2 ^ 59
def prefixEnd_7575264 : Nat := 4983230072969 + 3 ^ 40 * 7575264 * 2
def baseEnd_7575264 : Nat := 3889751516700754978462001

theorem tailTrace_7575264 : CollatzResearch.WordTrace tailWord_7575264 prefixEnd_7575264 3889751516700754978462001 := by
  unfold tailWord_7575264
  simp only [CollatzResearch.WordTrace]
  refine ⟨138146288214059877467722423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184195050952079836623629897 138146288214059877467722423)
  ·
    refine ⟨207219432321089816201583635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138146288214059877467722423 207219432321089816201583635)
    ·
      refine ⟨310829148481634724302375453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207219432321089816201583635 310829148481634724302375453)
      ·
        refine ⟨116560930680613021613390795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310829148481634724302375453 116560930680613021613390795)
        ·
          refine ⟨174841396020919532420086193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116560930680613021613390795 174841396020919532420086193)
          ·
            refine ⟨131131047015689649315064645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174841396020919532420086193 131131047015689649315064645)
            ·
              refine ⟨24587071315441809246574621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131131047015689649315064645 24587071315441809246574621)
              ·
                refine ⟨9220151743290678467465483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24587071315441809246574621 9220151743290678467465483)
                ·
                  refine ⟨13830227614936017701198225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220151743290678467465483 13830227614936017701198225)
                  ·
                    refine ⟨10372670711202013275898669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13830227614936017701198225 10372670711202013275898669)
                    ·
                      refine ⟨3889751516700754978462001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10372670711202013275898669 3889751516700754978462001)
                      ·
                        rfl

theorem cell23_7575264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_7575264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575264 prefixEnd_7575264 := by exact prefixLift 7575264
  have htrace : WordTrace (prefixWord ++ tailWord_7575264) baseStart_7575264 baseEnd_7575264 := by
    simpa [prefixWord, tailWord_7575264, baseEnd_7575264] using wordTrace_append hprefix tailTrace_7575264
  have hstable : (prefixWord ++ tailWord_7575264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575264).length < 2 ^ (prefixWord ++ tailWord_7575264).sum := by decide
  have hdescent : baseEnd_7575264 < baseStart_7575264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575327 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 2, 6]
def baseStart_7575327 : Nat := 118140960795 + 7575327 * 2 ^ 59
def prefixEnd_7575327 : Nat := 4983230072969 + 3 ^ 40 * 7575327 * 2
def baseEnd_7575327 : Nat := 1296594621993996077324737

theorem tailTrace_7575327 : CollatzResearch.WordTrace tailWord_7575327 prefixEnd_7575327 1296594621993996077324737 := by
  unfold tailWord_7575327
  simp only [CollatzResearch.WordTrace]
  refine ⟨276294874226891516694988235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184196582817927677796658823 276294874226891516694988235)
  ·
    refine ⟨414442311340337275042482353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276294874226891516694988235 414442311340337275042482353)
    ·
      refine ⟨310831733505252956281861765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414442311340337275042482353 310831733505252956281861765)
      ·
        refine ⟨58280950032234929302849081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 310831733505252956281861765 58280950032234929302849081)
        ·
          refine ⟨43710712524176196977136811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58280950032234929302849081 43710712524176196977136811)
          ·
            refine ⟨65566068786264295465705217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43710712524176196977136811 65566068786264295465705217)
            ·
              refine ⟨49174551589698221599278913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65566068786264295465705217 49174551589698221599278913)
              ·
                refine ⟨36880913692273666199459185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49174551589698221599278913 36880913692273666199459185)
                ·
                  refine ⟨27660685269205249649594389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36880913692273666199459185 27660685269205249649594389)
                  ·
                    refine ⟨1296594621993996077324737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27660685269205249649594389 1296594621993996077324737)
                    ·
                      rfl

theorem cell23_7575327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_7575327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575327 prefixEnd_7575327 := by exact prefixLift 7575327
  have htrace : WordTrace (prefixWord ++ tailWord_7575327) baseStart_7575327 baseEnd_7575327 := by
    simpa [prefixWord, tailWord_7575327, baseEnd_7575327] using wordTrace_append hprefix tailTrace_7575327
  have hstable : (prefixWord ++ tailWord_7575327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575327).length < 2 ^ (prefixWord ++ tailWord_7575327).sum := by decide
  have hdescent : baseEnd_7575327 < baseStart_7575327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575372 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 1, 3, 2]
def baseStart_7575372 : Nat := 118140960795 + 7575372 * 2 ^ 59
def prefixEnd_7575372 : Nat := 4983230072969 + 3 ^ 40 * 7575372 * 2
def baseEnd_7575372 : Nat := 3889806972611440555911505

theorem tailTrace_7575372 : CollatzResearch.WordTrace tailWord_7575372 prefixEnd_7575372 3889806972611440555911505 := by
  unfold tailWord_7575372
  simp only [CollatzResearch.WordTrace]
  refine ⟨138148257755864244690188185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184197677007818992920250913 138148257755864244690188185)
  ·
    refine ⟨103611193316898183517641139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138148257755864244690188185 103611193316898183517641139)
    ·
      refine ⟨155416789975347275276461709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103611193316898183517641139 155416789975347275276461709)
      ·
        refine ⟨58281296240755228228673141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155416789975347275276461709 58281296240755228228673141)
        ·
          refine ⟨5463871522570802646438107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58281296240755228228673141 5463871522570802646438107)
          ·
            refine ⟨8195807283856203969657161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463871522570802646438107 8195807283856203969657161)
            ·
              refine ⟨6146855462892152977242871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8195807283856203969657161 6146855462892152977242871)
              ·
                refine ⟨9220283194338229465864307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146855462892152977242871 9220283194338229465864307)
                ·
                  refine ⟨13830424791507344198796461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220283194338229465864307 13830424791507344198796461)
                  ·
                    refine ⟨5186409296815254074548673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13830424791507344198796461 5186409296815254074548673)
                    ·
                      refine ⟨3889806972611440555911505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5186409296815254074548673 3889806972611440555911505)
                      ·
                        rfl

theorem cell23_7575372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_7575372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575372 prefixEnd_7575372 := by exact prefixLift 7575372
  have htrace : WordTrace (prefixWord ++ tailWord_7575372) baseStart_7575372 baseEnd_7575372 := by
    simpa [prefixWord, tailWord_7575372, baseEnd_7575372] using wordTrace_append hprefix tailTrace_7575372
  have hstable : (prefixWord ++ tailWord_7575372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575372).length < 2 ^ (prefixWord ++ tailWord_7575372).sum := by decide
  have hdescent : baseEnd_7575372 < baseStart_7575372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575397 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7575397 : Nat := 118140960795 + 7575397 * 2 ^ 59
def prefixEnd_7575397 : Nat := 4983230072969 + 3 ^ 40 * 7575397 * 2
def baseEnd_7575397 : Nat := 3889819809627802958098889

theorem tailTrace_7575397 : CollatzResearch.WordTrace tailWord_7575397 prefixEnd_7575397 3889819809627802958098889 := by
  unfold tailWord_7575397
  simp only [CollatzResearch.WordTrace]
  refine ⟨276297427336637918650036445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184198284891091945766690963 276297427336637918650036445)
  ·
    refine ⟨103611535251239219493763667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276297427336637918650036445 103611535251239219493763667)
    ·
      refine ⟨155417302876858829240645501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103611535251239219493763667 155417302876858829240645501)
      ·
        refine ⟨58281488578822060965242063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155417302876858829240645501 58281488578822060965242063)
        ·
          refine ⟨87422232868233091447863095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58281488578822060965242063 87422232868233091447863095)
          ·
            refine ⟨131133349302349637171794643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87422232868233091447863095 131133349302349637171794643)
            ·
              refine ⟨196700023953524455757691965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131133349302349637171794643 196700023953524455757691965)
              ·
                refine ⟨73762508982571670909134487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196700023953524455757691965 73762508982571670909134487)
                ·
                  refine ⟨110643763473857506363701731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73762508982571670909134487 110643763473857506363701731)
                  ·
                    refine ⟨165965645210786259545552597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110643763473857506363701731 165965645210786259545552597)
                    ·
                      refine ⟨3889819809627802958098889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165965645210786259545552597 3889819809627802958098889)
                      ·
                        rfl

theorem cell23_7575397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7575397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575397 prefixEnd_7575397 := by exact prefixLift 7575397
  have htrace : WordTrace (prefixWord ++ tailWord_7575397) baseStart_7575397 baseEnd_7575397 := by
    simpa [prefixWord, tailWord_7575397, baseEnd_7575397] using wordTrace_append hprefix tailTrace_7575397
  have hstable : (prefixWord ++ tailWord_7575397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575397).length < 2 ^ (prefixWord ++ tailWord_7575397).sum := by decide
  have hdescent : baseEnd_7575397 < baseStart_7575397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575402 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_7575402 : Nat := 118140960795 + 7575402 * 2 ^ 59
def prefixEnd_7575402 : Nat := 4983230072969 + 3 ^ 40 * 7575402 * 2
def baseEnd_7575402 : Nat := 3889822377031075438536367

theorem tailTrace_7575402 : CollatzResearch.WordTrace tailWord_7575402 prefixEnd_7575402 3889822377031075438536367 := by
  unfold tailWord_7575402
  simp only [CollatzResearch.WordTrace]
  refine ⟨69074402425404951125992115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184198406467746536335978973 69074402425404951125992115)
  ·
    refine ⟨103611603638107426688988173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69074402425404951125992115 103611603638107426688988173)
    ·
      refine ⟨38854351364290285008370565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103611603638107426688988173 38854351364290285008370565)
      ·
        refine ⟨7285190880804428439069481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38854351364290285008370565 7285190880804428439069481)
        ·
          refine ⟨5463893160603321329302111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7285190880804428439069481 5463893160603321329302111)
          ·
            refine ⟨8195839740904981993953167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463893160603321329302111 8195839740904981993953167)
            ·
              refine ⟨12293759611357472990929751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195839740904981993953167 12293759611357472990929751)
              ·
                refine ⟨18440639417036209486394627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12293759611357472990929751 18440639417036209486394627)
                ·
                  refine ⟨27660959125554314229591941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18440639417036209486394627 27660959125554314229591941)
                  ·
                    refine ⟨5186429836041433918048489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27660959125554314229591941 5186429836041433918048489)
                    ·
                      refine ⟨3889822377031075438536367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5186429836041433918048489 3889822377031075438536367)
                      ·
                        rfl

theorem cell23_7575402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_7575402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575402 prefixEnd_7575402 := by exact prefixLift 7575402
  have htrace : WordTrace (prefixWord ++ tailWord_7575402) baseStart_7575402 baseEnd_7575402 := by
    simpa [prefixWord, tailWord_7575402, baseEnd_7575402] using wordTrace_append hprefix tailTrace_7575402
  have hstable : (prefixWord ++ tailWord_7575402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575402).length < 2 ^ (prefixWord ++ tailWord_7575402).sum := by decide
  have hdescent : baseEnd_7575402 < baseStart_7575402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575417 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 2, 8]
def baseStart_7575417 : Nat := 118140960795 + 7575417 * 2 ^ 59
def prefixEnd_7575417 : Nat := 4983230072969 + 3 ^ 40 * 7575417 * 2
def baseEnd_7575417 : Nat := 1296610026413630959949599

theorem tailTrace_7575417 : CollatzResearch.WordTrace tailWord_7575417 prefixEnd_7575417 1296610026413630959949599 := by
  unfold tailWord_7575417
  simp only [CollatzResearch.WordTrace]
  refine ⟨276298156796565462065764505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184198771197710308043843003 276298156796565462065764505)
  ·
    refine ⟨207223617597424096549323379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276298156796565462065764505 207223617597424096549323379)
    ·
      refine ⟨310835426396136144823985069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207223617597424096549323379 310835426396136144823985069)
      ·
        refine ⟨116563284898551054308994401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310835426396136144823985069 116563284898551054308994401)
        ·
          refine ⟨87422463673913290731745801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116563284898551054308994401 87422463673913290731745801)
          ·
            refine ⟨65566847755434968048809351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87422463673913290731745801 65566847755434968048809351)
            ·
              refine ⟨98350271633152452073214027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65566847755434968048809351 98350271633152452073214027)
              ·
                refine ⟨147525407449728678109821041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98350271633152452073214027 147525407449728678109821041)
                ·
                  refine ⟨110644055587296508582365781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147525407449728678109821041 110644055587296508582365781)
                  ·
                    refine ⟨1296610026413630959949599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110644055587296508582365781 1296610026413630959949599)
                    ·
                      rfl

theorem cell23_7575417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_7575417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575417 prefixEnd_7575417 := by exact prefixLift 7575417
  have htrace : WordTrace (prefixWord ++ tailWord_7575417) baseStart_7575417 baseEnd_7575417 := by
    simpa [prefixWord, tailWord_7575417, baseEnd_7575417] using wordTrace_append hprefix tailTrace_7575417
  have hstable : (prefixWord ++ tailWord_7575417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575417).length < 2 ^ (prefixWord ++ tailWord_7575417).sum := by decide
  have hdescent : baseEnd_7575417 < baseStart_7575417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575424 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_7575424 : Nat := 118140960795 + 7575424 * 2 ^ 59
def prefixEnd_7575424 : Nat := 4983230072969 + 3 ^ 40 * 7575424 * 2
def baseEnd_7575424 : Nat := 3889833673605474352461265

theorem tailTrace_7575424 : CollatzResearch.WordTrace tailWord_7575424 prefixEnd_7575424 3889833673605474352461265 := by
  unfold tailWord_7575424
  simp only [CollatzResearch.WordTrace]
  refine ⟨138149206053770051130634663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184198941405026734840846217 138149206053770051130634663)
  ·
    refine ⟨207223809080655076695951995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138149206053770051130634663 207223809080655076695951995)
    ·
      refine ⟨310835713620982615043927993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207223809080655076695951995 310835713620982615043927993)
      ·
        refine ⟨233126785215736961282945995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310835713620982615043927993 233126785215736961282945995)
        ·
          refine ⟨349690177823605441924418993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233126785215736961282945995 349690177823605441924418993)
          ·
            refine ⟨262267633367704081443314245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349690177823605441924418993 262267633367704081443314245)
            ·
              refine ⟨49175181256444515270621421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262267633367704081443314245 49175181256444515270621421)
              ·
                refine ⟨18440692971166693226483033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49175181256444515270621421 18440692971166693226483033)
                ·
                  refine ⟨13830519728375019919862275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18440692971166693226483033 13830519728375019919862275)
                  ·
                    refine ⟨20745779592562529879793413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13830519728375019919862275 20745779592562529879793413)
                    ·
                      refine ⟨3889833673605474352461265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20745779592562529879793413 3889833673605474352461265)
                      ·
                        rfl

theorem cell23_7575424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_7575424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575424 prefixEnd_7575424 := by exact prefixLift 7575424
  have htrace : WordTrace (prefixWord ++ tailWord_7575424) baseStart_7575424 baseEnd_7575424 := by
    simpa [prefixWord, tailWord_7575424, baseEnd_7575424] using wordTrace_append hprefix tailTrace_7575424
  have hstable : (prefixWord ++ tailWord_7575424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575424).length < 2 ^ (prefixWord ++ tailWord_7575424).sum := by decide
  have hdescent : baseEnd_7575424 < baseStart_7575424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575425 : List Nat := [1, 2, 4, 4, 1, 2, 1, 3, 5]
def baseStart_7575425 : Nat := 118140960795 + 7575425 * 2 ^ 59
def prefixEnd_7575425 : Nat := 4983230072969 + 3 ^ 40 * 7575425 * 2
def baseEnd_7575425 : Nat := 432203798565125427616529

theorem tailTrace_7575425 : CollatzResearch.WordTrace tailWord_7575425 prefixEnd_7575425 432203798565125427616529 := by
  unfold tailWord_7575425
  simp only [CollatzResearch.WordTrace]
  refine ⟨276298448580536479432055729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184198965720357652954703819 276298448580536479432055729)
  ·
    refine ⟨207223836435402359574041797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276298448580536479432055729 207223836435402359574041797)
    ·
      refine ⟨38854469331637942420132837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207223836435402359574041797 38854469331637942420132837)
      ·
        refine ⟨7285212999682114203774907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38854469331637942420132837 7285212999682114203774907)
        ·
          refine ⟨10927819499523171305662361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285212999682114203774907 10927819499523171305662361)
          ·
            refine ⟨8195864624642378479246771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10927819499523171305662361 8195864624642378479246771)
            ·
              refine ⟨12293796936963567718870157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195864624642378479246771 12293796936963567718870157)
              ·
                refine ⟨4610173851361337894576309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12293796936963567718870157 4610173851361337894576309)
                ·
                  refine ⟨432203798565125427616529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4610173851361337894576309 432203798565125427616529)
                  ·
                    rfl

theorem cell23_7575425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 5].length) (baseStart_7575425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575425 prefixEnd_7575425 := by exact prefixLift 7575425
  have htrace : WordTrace (prefixWord ++ tailWord_7575425) baseStart_7575425 baseEnd_7575425 := by
    simpa [prefixWord, tailWord_7575425, baseEnd_7575425] using wordTrace_append hprefix tailTrace_7575425
  have hstable : (prefixWord ++ tailWord_7575425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575425).length < 2 ^ (prefixWord ++ tailWord_7575425).sum := by decide
  have hdescent : baseEnd_7575425 < baseStart_7575425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575438 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_7575438 : Nat := 118140960795 + 7575438 * 2 ^ 59
def prefixEnd_7575438 : Nat := 4983230072969 + 3 ^ 40 * 7575438 * 2
def baseEnd_7575438 : Nat := 1296613620778212432562067

theorem tailTrace_7575438 : CollatzResearch.WordTrace tailWord_7575438 prefixEnd_7575438 1296613620778212432562067 := by
  unfold tailWord_7575438
  simp only [CollatzResearch.WordTrace]
  refine ⟨34537365341186172831534871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184199281819659588434852645 34537365341186172831534871)
  ·
    refine ⟨51806048011779259247302307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34537365341186172831534871 51806048011779259247302307)
    ·
      refine ⟨77709072017668888870953461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51806048011779259247302307 77709072017668888870953461)
      ·
        refine ⟨7285225501656458331651887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77709072017668888870953461 7285225501656458331651887)
        ·
          refine ⟨10927838252484687497477831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7285225501656458331651887 10927838252484687497477831)
          ·
            refine ⟨16391757378727031246216747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10927838252484687497477831 16391757378727031246216747)
            ·
              refine ⟨24587636068090546869325121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16391757378727031246216747 24587636068090546869325121)
              ·
                refine ⟨18440727051067910151993841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24587636068090546869325121 18440727051067910151993841)
                ·
                  refine ⟨13830545288300932613995381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18440727051067910151993841 13830545288300932613995381)
                  ·
                    refine ⟨1296613620778212432562067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13830545288300932613995381 1296613620778212432562067)
                    ·
                      rfl

theorem cell23_7575438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_7575438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575438 prefixEnd_7575438 := by exact prefixLift 7575438
  have htrace : WordTrace (prefixWord ++ tailWord_7575438) baseStart_7575438 baseEnd_7575438 := by
    simpa [prefixWord, tailWord_7575438, baseEnd_7575438] using wordTrace_append hprefix tailTrace_7575438
  have hstable : (prefixWord ++ tailWord_7575438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575438).length < 2 ^ (prefixWord ++ tailWord_7575438).sum := by decide
  have hdescent : baseEnd_7575438 < baseStart_7575438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575474 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_7575474 : Nat := 118140960795 + 7575474 * 2 ^ 59
def prefixEnd_7575474 : Nat := 4983230072969 + 3 ^ 40 * 7575474 * 2
def baseEnd_7575474 : Nat := 3889859347638199156836035

theorem tailTrace_7575474 : CollatzResearch.WordTrace tailWord_7575474 prefixEnd_7575474 3889859347638199156836035 := by
  unfold tailWord_7575474
  simp only [CollatzResearch.WordTrace]
  refine ⟨69075058939339740200147369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184200157171572640533726317 69075058939339740200147369)
  ·
    refine ⟨51806294204504805150110527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69075058939339740200147369 51806294204504805150110527)
    ·
      refine ⟨77709441306757207725165791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51806294204504805150110527 77709441306757207725165791)
      ·
        refine ⟨116564161960135811587748687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77709441306757207725165791 116564161960135811587748687)
        ·
          refine ⟨174846242940203717381623031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116564161960135811587748687 174846242940203717381623031)
          ·
            refine ⟨262269364410305576072434547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174846242940203717381623031 262269364410305576072434547)
            ·
              refine ⟨393404046615458364108651821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262269364410305576072434547 393404046615458364108651821)
              ·
                refine ⟨147526517480796886540744433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393404046615458364108651821 147526517480796886540744433)
                ·
                  refine ⟨110644888110597664905558325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147526517480796886540744433 110644888110597664905558325)
                  ·
                    refine ⟨10372958260368531084896093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110644888110597664905558325 10372958260368531084896093)
                    ·
                      refine ⟨3889859347638199156836035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10372958260368531084896093 3889859347638199156836035)
                      ·
                        rfl

theorem cell23_7575474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_7575474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575474 prefixEnd_7575474 := by exact prefixLift 7575474
  have htrace : WordTrace (prefixWord ++ tailWord_7575474) baseStart_7575474 baseEnd_7575474 := by
    simpa [prefixWord, tailWord_7575474, baseEnd_7575474] using wordTrace_append hprefix tailTrace_7575474
  have hstable : (prefixWord ++ tailWord_7575474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575474).length < 2 ^ (prefixWord ++ tailWord_7575474).sum := by decide
  have hdescent : baseEnd_7575474 < baseStart_7575474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575508 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_7575508 : Nat := 118140960795 + 7575508 * 2 ^ 59
def prefixEnd_7575508 : Nat := 4983230072969 + 3 ^ 40 * 7575508 * 2
def baseEnd_7575508 : Nat := 3889876805980452023810879

theorem tailTrace_7575508 : CollatzResearch.WordTrace tailWord_7575508 prefixEnd_7575508 3889876805980452023810879 := by
  unfold tailWord_7575508
  simp only [CollatzResearch.WordTrace]
  refine ⟨138150737919617892303663589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184200983892823856404884785 138150737919617892303663589)
  ·
    refine ⟨25903263359928354806936923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138150737919617892303663589 25903263359928354806936923)
    ·
      refine ⟨38854895039892532210405385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25903263359928354806936923 38854895039892532210405385)
      ·
        refine ⟨29141171279919399157804039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38854895039892532210405385 29141171279919399157804039)
        ·
          refine ⟨43711756919879098736706059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29141171279919399157804039 43711756919879098736706059)
          ·
            refine ⟨65567635379818648105059089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43711756919879098736706059 65567635379818648105059089)
            ·
              refine ⟨49175726534863986078794317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65567635379818648105059089 49175726534863986078794317)
              ·
                refine ⟨18440897450573994779547869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49175726534863986078794317 18440897450573994779547869)
                ·
                  refine ⟨6915336543965248042330451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18440897450573994779547869 6915336543965248042330451)
                  ·
                    refine ⟨10373004815947872063495677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6915336543965248042330451 10373004815947872063495677)
                    ·
                      refine ⟨3889876805980452023810879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10373004815947872063495677 3889876805980452023810879)
                      ·
                        rfl

theorem cell23_7575508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_7575508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575508 prefixEnd_7575508 := by exact prefixLift 7575508
  have htrace : WordTrace (prefixWord ++ tailWord_7575508) baseStart_7575508 baseEnd_7575508 := by
    simpa [prefixWord, tailWord_7575508, baseEnd_7575508] using wordTrace_append hprefix tailTrace_7575508
  have hstable : (prefixWord ++ tailWord_7575508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575508).length < 2 ^ (prefixWord ++ tailWord_7575508).sum := by decide
  have hdescent : baseEnd_7575508 < baseStart_7575508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575548 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_7575548 : Nat := 118140960795 + 7575548 * 2 ^ 59
def prefixEnd_7575548 : Nat := 4983230072969 + 3 ^ 40 * 7575548 * 2
def baseEnd_7575548 : Nat := 3889897345206631867310695

theorem tailTrace_7575548 : CollatzResearch.WordTrace tailWord_7575548 prefixEnd_7575548 3889897345206631867310695 := by
  unfold tailWord_7575548
  simp only [CollatzResearch.WordTrace]
  refine ⟨138151467379545435719391649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184201956506060580959188865 138151467379545435719391649)
  ·
    refine ⟨103613600534659076789543737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138151467379545435719391649 103613600534659076789543737)
    ·
      refine ⟨77710200400994307592157803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103613600534659076789543737 77710200400994307592157803)
      ·
        refine ⟨116565300601491461388236705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77710200400994307592157803 116565300601491461388236705)
        ·
          refine ⟨87423975451118596041177529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116565300601491461388236705 87423975451118596041177529)
          ·
            refine ⟨65567981588338947030883147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87423975451118596041177529 65567981588338947030883147)
            ·
              refine ⟨98351972382508420546324721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65567981588338947030883147 98351972382508420546324721)
              ·
                refine ⟨73763979286881315409743541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98351972382508420546324721 73763979286881315409743541)
                ·
                  refine ⟨6915373058145123319663457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73763979286881315409743541 6915373058145123319663457)
                  ·
                    refine ⟨5186529793608842489747593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6915373058145123319663457 5186529793608842489747593)
                    ·
                      refine ⟨3889897345206631867310695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5186529793608842489747593 3889897345206631867310695)
                      ·
                        rfl

theorem cell23_7575548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_7575548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575548 prefixEnd_7575548 := by exact prefixLift 7575548
  have htrace : WordTrace (prefixWord ++ tailWord_7575548) baseStart_7575548 baseEnd_7575548 := by
    simpa [prefixWord, tailWord_7575548, baseEnd_7575548] using wordTrace_append hprefix tailTrace_7575548
  have hstable : (prefixWord ++ tailWord_7575548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575548).length < 2 ^ (prefixWord ++ tailWord_7575548).sum := by decide
  have hdescent : baseEnd_7575548 < baseStart_7575548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575575 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 1, 6]
def baseStart_7575575 : Nat := 118140960795 + 7575575 * 2 ^ 59
def prefixEnd_7575575 : Nat := 4983230072969 + 3 ^ 40 * 7575575 * 2
def baseEnd_7575575 : Nat := 1296637069728101087224357

theorem tailTrace_7575575 : CollatzResearch.WordTrace tailWord_7575575 prefixEnd_7575575 1296637069728101087224357 := by
  unfold tailWord_7575575
  simp only [CollatzResearch.WordTrace]
  refine ⟨276303919529993055050016179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184202613019995370033344119 276303919529993055050016179)
  ·
    refine ⟨414455879294989582575024269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276303919529993055050016179 414455879294989582575024269)
    ·
      refine ⟨155420954735621093465634101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414455879294989582575024269 155420954735621093465634101)
      ·
        refine ⟨14570714506464477512403197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155420954735621093465634101 14570714506464477512403197)
        ·
          refine ⟨5464017939924179067151199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14570714506464477512403197 5464017939924179067151199)
          ·
            refine ⟨8196026909886268600726799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464017939924179067151199 8196026909886268600726799)
            ·
              refine ⟨12294040364829402901090199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196026909886268600726799 12294040364829402901090199)
              ·
                refine ⟨18441060547244104351635299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12294040364829402901090199 18441060547244104351635299)
                ·
                  refine ⟨27661590820866156527452949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18441060547244104351635299 27661590820866156527452949)
                  ·
                    refine ⟨1296637069728101087224357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27661590820866156527452949 1296637069728101087224357)
                    ·
                      rfl

theorem cell23_7575575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_7575575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575575 prefixEnd_7575575 := by exact prefixLift 7575575
  have htrace : WordTrace (prefixWord ++ tailWord_7575575) baseStart_7575575 baseEnd_7575575 := by
    simpa [prefixWord, tailWord_7575575, baseEnd_7575575] using wordTrace_append hprefix tailTrace_7575575
  have hstable : (prefixWord ++ tailWord_7575575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575575).length < 2 ^ (prefixWord ++ tailWord_7575575).sum := by decide
  have hdescent : baseEnd_7575575 < baseStart_7575575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575578 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_7575578 : Nat := 118140960795 + 7575578 * 2 ^ 59
def prefixEnd_7575578 : Nat := 4983230072969 + 3 ^ 40 * 7575578 * 2
def baseEnd_7575578 : Nat := 3889912749626266749935557

theorem tailTrace_7575578 : CollatzResearch.WordTrace tailWord_7575578 prefixEnd_7575578 3889912749626266749935557 := by
  unfold tailWord_7575578
  simp only [CollatzResearch.WordTrace]
  refine ⟨69076007237245546640593847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184202685965988124374916925 69076007237245546640593847)
  ·
    refine ⟨103614010855868319960890771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69076007237245546640593847 103614010855868319960890771)
    ·
      refine ⟨155421016283802479941336157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103614010855868319960890771 155421016283802479941336157)
      ·
        refine ⟨58282881106425929978001059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155421016283802479941336157 58282881106425929978001059)
        ·
          refine ⟨87424321659638894967001589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58282881106425929978001059 87424321659638894967001589)
          ·
            refine ⟨8196030155591146403156399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87424321659638894967001589 8196030155591146403156399)
            ·
              refine ⟨12294045233386719604734599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196030155591146403156399 12294045233386719604734599)
              ·
                refine ⟨18441067850080079407101899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12294045233386719604734599 18441067850080079407101899)
                ·
                  refine ⟨27661601775120119110652849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18441067850080079407101899 27661601775120119110652849)
                  ·
                    refine ⟨20746201331340089332989637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27661601775120119110652849 20746201331340089332989637)
                    ·
                      refine ⟨3889912749626266749935557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20746201331340089332989637 3889912749626266749935557)
                      ·
                        rfl

theorem cell23_7575578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_7575578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575578 prefixEnd_7575578 := by exact prefixLift 7575578
  have htrace : WordTrace (prefixWord ++ tailWord_7575578) baseStart_7575578 baseEnd_7575578 := by
    simpa [prefixWord, tailWord_7575578, baseEnd_7575578] using wordTrace_append hprefix tailTrace_7575578
  have hstable : (prefixWord ++ tailWord_7575578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575578).length < 2 ^ (prefixWord ++ tailWord_7575578).sum := by decide
  have hdescent : baseEnd_7575578 < baseStart_7575578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575585 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_7575585 : Nat := 118140960795 + 7575585 * 2 ^ 59
def prefixEnd_7575585 : Nat := 4983230072969 + 3 ^ 40 * 7575585 * 2
def baseEnd_7575585 : Nat := 3889916343990848222548025

theorem tailTrace_7575585 : CollatzResearch.WordTrace tailWord_7575585 prefixEnd_7575585 3889916343990848222548025 := by
  unfold tailWord_7575585
  simp only [CollatzResearch.WordTrace]
  refine ⟨276304284259956826757880209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184202856173304551171920139 276304284259956826757880209)
  ·
    refine ⟨207228213194967620068410157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276304284259956826757880209 207228213194967620068410157)
    ·
      refine ⟨77710579948112857525653809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207228213194967620068410157 77710579948112857525653809)
      ·
        refine ⟨58282934961084643144240357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77710579948112857525653809 58282934961084643144240357)
        ·
          refine ⟨10928050305203370589545067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58282934961084643144240357 10928050305203370589545067)
          ·
            refine ⟨16392075457805055884317601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10928050305203370589545067 16392075457805055884317601)
            ·
              refine ⟨12294056593353791913238201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16392075457805055884317601 12294056593353791913238201)
              ·
                refine ⟨9220542445015343934928651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12294056593353791913238201 9220542445015343934928651)
                ·
                  refine ⟨13830813667523015902392977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220542445015343934928651 13830813667523015902392977)
                  ·
                    refine ⟨10373110250642261926794733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13830813667523015902392977 10373110250642261926794733)
                    ·
                      refine ⟨3889916343990848222548025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10373110250642261926794733 3889916343990848222548025)
                      ·
                        rfl

theorem cell23_7575585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_7575585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575585 prefixEnd_7575585 := by exact prefixLift 7575585
  have htrace : WordTrace (prefixWord ++ tailWord_7575585) baseStart_7575585 baseEnd_7575585 := by
    simpa [prefixWord, tailWord_7575585, baseEnd_7575585] using wordTrace_append hprefix tailTrace_7575585
  have hstable : (prefixWord ++ tailWord_7575585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575585).length < 2 ^ (prefixWord ++ tailWord_7575585).sum := by decide
  have hdescent : baseEnd_7575585 < baseStart_7575585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575688 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7575688 : Nat := 118140960795 + 7575688 * 2 ^ 59
def prefixEnd_7575688 : Nat := 4983230072969 + 3 ^ 40 * 7575688 * 2
def baseEnd_7575688 : Nat := 3889969232498261319560051

theorem tailTrace_7575688 : CollatzResearch.WordTrace tailWord_7575688 prefixEnd_7575688 3889969232498261319560051 := by
  unfold tailWord_7575688
  simp only [CollatzResearch.WordTrace]
  refine ⟨138154020489291837674439859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184205360652389116899253145 138154020489291837674439859)
  ·
    refine ⟨207231030733937756511659789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138154020489291837674439859 207231030733937756511659789)
    ·
      refine ⟨77711636525226658691872421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207231030733937756511659789 77711636525226658691872421)
      ·
        refine ⟨14570931848479998504726079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77711636525226658691872421 14570931848479998504726079)
        ·
          refine ⟨21856397772719997757089119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14570931848479998504726079 21856397772719997757089119)
          ·
            refine ⟨32784596659079996635633679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21856397772719997757089119 32784596659079996635633679)
            ·
              refine ⟨49176894988619994953450519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32784596659079996635633679 49176894988619994953450519)
              ·
                refine ⟨73765342482929992430175779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49176894988619994953450519 73765342482929992430175779)
                ·
                  refine ⟨110648013724394988645263669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73765342482929992430175779 110648013724394988645263669)
                  ·
                    refine ⟨10373251286662030185493469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110648013724394988645263669 10373251286662030185493469)
                    ·
                      refine ⟨3889969232498261319560051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10373251286662030185493469 3889969232498261319560051)
                      ·
                        rfl

theorem cell23_7575688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7575688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575688 prefixEnd_7575688 := by exact prefixLift 7575688
  have htrace : WordTrace (prefixWord ++ tailWord_7575688) baseStart_7575688 baseEnd_7575688 := by
    simpa [prefixWord, tailWord_7575688, baseEnd_7575688] using wordTrace_append hprefix tailTrace_7575688
  have hstable : (prefixWord ++ tailWord_7575688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575688).length < 2 ^ (prefixWord ++ tailWord_7575688).sum := by decide
  have hdescent : baseEnd_7575688 < baseStart_7575688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575738 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_7575738 : Nat := 118140960795 + 7575738 * 2 ^ 59
def prefixEnd_7575738 : Nat := 4983230072969 + 3 ^ 40 * 7575738 * 2
def baseEnd_7575738 : Nat := 1296664968843662041311607

theorem tailTrace_7575738 : CollatzResearch.WordTrace tailWord_7575738 prefixEnd_7575738 1296664968843662041311607 := by
  unfold tailWord_7575738
  simp only [CollatzResearch.WordTrace]
  refine ⟨69077466157100633472049967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184206576418935022592133245 69077466157100633472049967)
  ·
    refine ⟨103616199235650950208074951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69077466157100633472049967 103616199235650950208074951)
    ·
      refine ⟨155424298853476425312112427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103616199235650950208074951 155424298853476425312112427)
      ·
        refine ⟨233136448280214637968168641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155424298853476425312112427 233136448280214637968168641)
        ·
          refine ⟨174852336210160978476126481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233136448280214637968168641 174852336210160978476126481)
          ·
            refine ⟨131139252157620733857094861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174852336210160978476126481 131139252157620733857094861)
            ·
              refine ⟨49177219559107775196410573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131139252157620733857094861 49177219559107775196410573)
              ·
                refine ⟨18441457334665415698653965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49177219559107775196410573 18441457334665415698653965)
                ·
                  refine ⟨6915546500499530886995237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18441457334665415698653965 6915546500499530886995237)
                  ·
                    refine ⟨1296664968843662041311607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6915546500499530886995237 1296664968843662041311607)
                    ·
                      rfl

theorem cell23_7575738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_7575738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575738 prefixEnd_7575738 := by exact prefixLift 7575738
  have htrace : WordTrace (prefixWord ++ tailWord_7575738) baseStart_7575738 baseEnd_7575738 := by
    simpa [prefixWord, tailWord_7575738, baseEnd_7575738] using wordTrace_append hprefix tailTrace_7575738
  have hstable : (prefixWord ++ tailWord_7575738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575738).length < 2 ^ (prefixWord ++ tailWord_7575738).sum := by decide
  have hdescent : baseEnd_7575738 < baseStart_7575738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575741 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7575741 : Nat := 118140960795 + 7575741 * 2 ^ 59
def prefixEnd_7575741 : Nat := 4983230072969 + 3 ^ 40 * 7575741 * 2
def baseEnd_7575741 : Nat := 3889996446972949612197307

theorem tailTrace_7575741 : CollatzResearch.WordTrace tailWord_7575741 prefixEnd_7575741 3889996446972949612197307 := by
  unfold tailWord_7575741
  simp only [CollatzResearch.WordTrace]
  refine ⟨276309974047391665400559077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184206649364927776933706051 276309974047391665400559077)
  ·
    refine ⟨51808120133885937262604827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276309974047391665400559077 51808120133885937262604827)
    ·
      refine ⟨77712180200828905893907241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51808120133885937262604827 77712180200828905893907241)
      ·
        refine ⟨58284135150621679420430431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77712180200828905893907241 58284135150621679420430431)
        ·
          refine ⟨87426202725932519130645647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58284135150621679420430431 87426202725932519130645647)
          ·
            refine ⟨131139304088898778695968471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87426202725932519130645647 131139304088898778695968471)
            ·
              refine ⟨196708956133348168043952707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131139304088898778695968471 196708956133348168043952707)
              ·
                refine ⟨295063434200022252065929061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196708956133348168043952707 295063434200022252065929061)
                ·
                  refine ⟨55324393912504172262361699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295063434200022252065929061 55324393912504172262361699)
                  ·
                    refine ⟨82986590868756258393542549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55324393912504172262361699 82986590868756258393542549)
                    ·
                      refine ⟨3889996446972949612197307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82986590868756258393542549 3889996446972949612197307)
                      ·
                        rfl

theorem cell23_7575741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7575741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575741 prefixEnd_7575741 := by exact prefixLift 7575741
  have htrace : WordTrace (prefixWord ++ tailWord_7575741) baseStart_7575741 baseEnd_7575741 := by
    simpa [prefixWord, tailWord_7575741, baseEnd_7575741] using wordTrace_append hprefix tailTrace_7575741
  have hstable : (prefixWord ++ tailWord_7575741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575741).length < 2 ^ (prefixWord ++ tailWord_7575741).sum := by decide
  have hdescent : baseEnd_7575741 < baseStart_7575741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575789 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_7575789 : Nat := 118140960795 + 7575789 * 2 ^ 59
def prefixEnd_7575789 : Nat := 4983230072969 + 3 ^ 40 * 7575789 * 2
def baseEnd_7575789 : Nat := 1296673698014788474799029

theorem tailTrace_7575789 : CollatzResearch.WordTrace tailWord_7575789 prefixEnd_7575789 1296673698014788474799029 := by
  unfold tailWord_7575789
  simp only [CollatzResearch.WordTrace]
  refine ⟨276311724751217769598306421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184207816500811846398870947 276311724751217769598306421)
  ·
    refine ⟨25904224195426665899841227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276311724751217769598306421 25904224195426665899841227)
    ·
      refine ⟨38856336293139998849761841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25904224195426665899841227 38856336293139998849761841)
      ·
        refine ⟨29142252219854999137321381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38856336293139998849761841 29142252219854999137321381)
        ·
          refine ⟨5464172291222812338247759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29142252219854999137321381 5464172291222812338247759)
          ·
            refine ⟨8196258436834218507371639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464172291222812338247759 8196258436834218507371639)
            ·
              refine ⟨12294387655251327761057459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196258436834218507371639 12294387655251327761057459)
              ·
                refine ⟨18441581482876991641586189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12294387655251327761057459 18441581482876991641586189)
                ·
                  refine ⟨6915593056078871865594821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18441581482876991641586189 6915593056078871865594821)
                  ·
                    refine ⟨1296673698014788474799029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6915593056078871865594821 1296673698014788474799029)
                    ·
                      rfl

theorem cell23_7575789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_7575789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575789 prefixEnd_7575789 := by exact prefixLift 7575789
  have htrace : WordTrace (prefixWord ++ tailWord_7575789) baseStart_7575789 baseEnd_7575789 := by
    simpa [prefixWord, tailWord_7575789, baseEnd_7575789] using wordTrace_append hprefix tailTrace_7575789
  have hstable : (prefixWord ++ tailWord_7575789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575789).length < 2 ^ (prefixWord ++ tailWord_7575789).sum := by decide
  have hdescent : baseEnd_7575789 < baseStart_7575789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575822 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2]
def baseStart_7575822 : Nat := 118140960795 + 7575822 * 2 ^ 59
def prefixEnd_7575822 : Nat := 4983230072969 + 3 ^ 40 * 7575822 * 2
def baseEnd_7575822 : Nat := 3890038038905963795284435

theorem tailTrace_7575822 : CollatzResearch.WordTrace tailWord_7575822 prefixEnd_7575822 3890038038905963795284435 := by
  unfold tailWord_7575822
  simp only [CollatzResearch.WordTrace]
  refine ⟨34539116045012277029282215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184208618906732144156171813 34539116045012277029282215)
  ·
    refine ⟨51808674067518415543923323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34539116045012277029282215 51808674067518415543923323)
    ·
      refine ⟨77713011101277623315884985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51808674067518415543923323 77713011101277623315884985)
      ·
        refine ⟨58284758325958217486913739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77713011101277623315884985 58284758325958217486913739)
        ·
          refine ⟨87427137488937326230370609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58284758325958217486913739 87427137488937326230370609)
          ·
            refine ⟨65570353116702994672777957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87427137488937326230370609 65570353116702994672777957)
            ·
              refine ⟨12294441209381811501145867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65570353116702994672777957 12294441209381811501145867)
              ·
                refine ⟨18441661814072717251718801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12294441209381811501145867 18441661814072717251718801)
                ·
                  refine ⟨13831246360554537938789101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18441661814072717251718801 13831246360554537938789101)
                  ·
                    refine ⟨5186717385207951727045913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13831246360554537938789101 5186717385207951727045913)
                    ·
                      refine ⟨3890038038905963795284435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5186717385207951727045913 3890038038905963795284435)
                      ·
                        rfl

theorem cell23_7575822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_7575822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575822 prefixEnd_7575822 := by exact prefixLift 7575822
  have htrace : WordTrace (prefixWord ++ tailWord_7575822) baseStart_7575822 baseEnd_7575822 := by
    simpa [prefixWord, tailWord_7575822, baseEnd_7575822] using wordTrace_append hprefix tailTrace_7575822
  have hstable : (prefixWord ++ tailWord_7575822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575822).length < 2 ^ (prefixWord ++ tailWord_7575822).sum := by decide
  have hdescent : baseEnd_7575822 < baseStart_7575822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575865 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7575865 : Nat := 118140960795 + 7575865 * 2 ^ 59
def prefixEnd_7575865 : Nat := 4983230072969 + 3 ^ 40 * 7575865 * 2
def baseEnd_7575865 : Nat := 3890060118574107127046737

theorem tailTrace_7575865 : CollatzResearch.WordTrace tailWord_7575865 prefixEnd_7575865 3890060118574107127046737 := by
  unfold tailWord_7575865
  simp only [CollatzResearch.WordTrace]
  refine ⟨276314496698942434578073049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184209664465961623052048699 276314496698942434578073049)
  ·
    refine ⟨207235872524206825933554787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276314496698942434578073049 207235872524206825933554787)
    ·
      refine ⟨310853808786310238900332181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207235872524206825933554787 310853808786310238900332181)
      ·
        refine ⟨14571272286858292448453071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 310853808786310238900332181 14571272286858292448453071)
        ·
          refine ⟨21856908430287438672679607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14571272286858292448453071 21856908430287438672679607)
          ·
            refine ⟨32785362645431158009019411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21856908430287438672679607 32785362645431158009019411)
            ·
              refine ⟨49178043968146737013529117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32785362645431158009019411 49178043968146737013529117)
              ·
                refine ⟨18441766488055026380073419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49178043968146737013529117 18441766488055026380073419)
                ·
                  refine ⟨27662649732082539570110129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18441766488055026380073419 27662649732082539570110129)
                  ·
                    refine ⟨20746987299061904677582597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27662649732082539570110129 20746987299061904677582597)
                    ·
                      refine ⟨3890060118574107127046737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20746987299061904677582597 3890060118574107127046737)
                      ·
                        rfl

theorem cell23_7575865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7575865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575865 prefixEnd_7575865 := by exact prefixLift 7575865
  have htrace : WordTrace (prefixWord ++ tailWord_7575865) baseStart_7575865 baseEnd_7575865 := by
    simpa [prefixWord, tailWord_7575865, baseEnd_7575865] using wordTrace_append hprefix tailTrace_7575865
  have hstable : (prefixWord ++ tailWord_7575865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575865).length < 2 ^ (prefixWord ++ tailWord_7575865).sum := by decide
  have hdescent : baseEnd_7575865 < baseStart_7575865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575889 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 1, 2, 3]
def baseStart_7575889 : Nat := 118140960795 + 7575889 * 2 ^ 59
def prefixEnd_7575889 : Nat := 4983230072969 + 3 ^ 40 * 7575889 * 2
def baseEnd_7575889 : Nat := 3890072442109815033146627

theorem tailTrace_7575889 : CollatzResearch.WordTrace tailWord_7575889 prefixEnd_7575889 3890072442109815033146627 := by
  unfold tailWord_7575889
  simp only [CollatzResearch.WordTrace]
  refine ⟨276315372050855486676946721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184210248033903657784631147 276315372050855486676946721)
  ·
    refine ⟨207236529038141615007710041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276315372050855486676946721 207236529038141615007710041)
    ·
      refine ⟨155427396778606211255782531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207236529038141615007710041 155427396778606211255782531)
      ·
        refine ⟨233141095167909316883673797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155427396778606211255782531 233141095167909316883673797)
        ·
          refine ⟨43713955343982996915688837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233141095167909316883673797 43713955343982996915688837)
          ·
            refine ⟨8196366626996811921691657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43713955343982996915688837 8196366626996811921691657)
            ·
              refine ⟨6147274970247608941268743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8196366626996811921691657 6147274970247608941268743)
              ·
                refine ⟨9220912455371413411903115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6147274970247608941268743 9220912455371413411903115)
                ·
                  refine ⟨13831368683057120117854673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220912455371413411903115 13831368683057120117854673)
                  ·
                    refine ⟨10373526512292840088391005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13831368683057120117854673 10373526512292840088391005)
                    ·
                      refine ⟨3890072442109815033146627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10373526512292840088391005 3890072442109815033146627)
                      ·
                        rfl

theorem cell23_7575889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_7575889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575889 prefixEnd_7575889 := by exact prefixLift 7575889
  have htrace : WordTrace (prefixWord ++ tailWord_7575889) baseStart_7575889 baseEnd_7575889 := by
    simpa [prefixWord, tailWord_7575889, baseEnd_7575889] using wordTrace_append hprefix tailTrace_7575889
  have hstable : (prefixWord ++ tailWord_7575889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575889).length < 2 ^ (prefixWord ++ tailWord_7575889).sum := by decide
  have hdescent : baseEnd_7575889 < baseStart_7575889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575926 : List Nat := [5, 1, 1, 4, 2, 1, 2, 7]
def baseStart_7575926 : Nat := 118140960795 + 7575926 * 2 ^ 59
def prefixEnd_7575926 : Nat := 4983230072969 + 3 ^ 40 * 7575926 * 2
def baseEnd_7575926 : Nat := 144077460773853014384591

theorem tailTrace_7575926 : CollatzResearch.WordTrace tailWord_7575926 prefixEnd_7575926 144077460773853014384591 := by
  unfold tailWord_7575926
  simp only [CollatzResearch.WordTrace]
  refine ⟨17269795096982590124752727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184211147701147627997362421 17269795096982590124752727)
  ·
    refine ⟨25904692645473885187129091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17269795096982590124752727 25904692645473885187129091)
    ·
      refine ⟨38857038968210827780693637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25904692645473885187129091 38857038968210827780693637)
      ·
        refine ⟨7285694806539530208880057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38857038968210827780693637 7285694806539530208880057)
        ·
          refine ⟨5464271104904647656660043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7285694806539530208880057 5464271104904647656660043)
          ·
            refine ⟨8196406657356971484990065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464271104904647656660043 8196406657356971484990065)
            ·
              refine ⟨6147304993017728613742549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8196406657356971484990065 6147304993017728613742549)
              ·
                refine ⟨144077460773853014384591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6147304993017728613742549 144077460773853014384591)
                ·
                  rfl

theorem cell23_7575926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_7575926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575926 prefixEnd_7575926 := by exact prefixLift 7575926
  have htrace : WordTrace (prefixWord ++ tailWord_7575926) baseStart_7575926 baseEnd_7575926 := by
    simpa [prefixWord, tailWord_7575926, baseEnd_7575926] using wordTrace_append hprefix tailTrace_7575926
  have hstable : (prefixWord ++ tailWord_7575926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575926).length < 2 ^ (prefixWord ++ tailWord_7575926).sum := by decide
  have hdescent : baseEnd_7575926 < baseStart_7575926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7575945 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_7575945 : Nat := 118140960795 + 7575945 * 2 ^ 59
def prefixEnd_7575945 : Nat := 4983230072969 + 3 ^ 40 * 7575945 * 2
def baseEnd_7575945 : Nat := 3890101197026466814046369

theorem tailTrace_7575945 : CollatzResearch.WordTrace tailWord_7575945 prefixEnd_7575945 3890101197026466814046369 := by
  unfold tailWord_7575945
  simp only [CollatzResearch.WordTrace]
  refine ⟨276317414538652608240985289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184211609692435072160656859 276317414538652608240985289)
  ·
    refine ⟨207238060903989456180738967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276317414538652608240985289 207238060903989456180738967)
    ·
      refine ⟨310857091355984184271108451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207238060903989456180738967 310857091355984184271108451)
      ·
        refine ⟨466285637033976276406662677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310857091355984184271108451 466285637033976276406662677)
        ·
          refine ⟨21857139235967637956562313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 466285637033976276406662677 21857139235967637956562313)
          ·
            refine ⟨16392854426975728467421735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21857139235967637956562313 16392854426975728467421735)
            ·
              refine ⟨24589281640463592701132603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16392854426975728467421735 24589281640463592701132603)
              ·
                refine ⟨36883922460695389051698905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24589281640463592701132603 36883922460695389051698905)
                ·
                  refine ⟨27662941845521541788774179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36883922460695389051698905 27662941845521541788774179)
                  ·
                    refine ⟨41494412768282312683161269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27662941845521541788774179 41494412768282312683161269)
                    ·
                      refine ⟨3890101197026466814046369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41494412768282312683161269 3890101197026466814046369)
                      ·
                        rfl

theorem cell23_7575945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_7575945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7575945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7575945 prefixEnd_7575945 := by exact prefixLift 7575945
  have htrace : WordTrace (prefixWord ++ tailWord_7575945) baseStart_7575945 baseEnd_7575945 := by
    simpa [prefixWord, tailWord_7575945, baseEnd_7575945] using wordTrace_append hprefix tailTrace_7575945
  have hstable : (prefixWord ++ tailWord_7575945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7575945).length < 2 ^ (prefixWord ++ tailWord_7575945).sum := by decide
  have hdescent : baseEnd_7575945 < baseStart_7575945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7575945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576022 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7576022 : Nat := 118140960795 + 7576022 * 2 ^ 59
def prefixEnd_7576022 : Nat := 4983230072969 + 3 ^ 40 * 7576022 * 2
def baseEnd_7576022 : Nat := 3890140735036863012783515

theorem tailTrace_7576022 : CollatzResearch.WordTrace tailWord_7576022 prefixEnd_7576022 3890140735036863012783515 := by
  unfold tailWord_7576022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17270013934960853149471145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184213481972915766927692213 17270013934960853149471145)
  ·
    refine ⟨12952510451220639862103359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17270013934960853149471145 12952510451220639862103359)
    ·
      refine ⟨19428765676830959793155039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12952510451220639862103359 19428765676830959793155039)
      ·
        refine ⟨29143148515246439689732559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19428765676830959793155039 29143148515246439689732559)
        ·
          refine ⟨43714722772869659534598839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29143148515246439689732559 43714722772869659534598839)
          ·
            refine ⟨65572084159304489301898259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43714722772869659534598839 65572084159304489301898259)
            ·
              refine ⟨98358126238956733952847389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65572084159304489301898259 98358126238956733952847389)
              ·
                refine ⟨36884297339608775232317771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98358126238956733952847389 36884297339608775232317771)
                ·
                  refine ⟨55326446009413162848476657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36884297339608775232317771 55326446009413162848476657)
                  ·
                    refine ⟨41494834507059872136357493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55326446009413162848476657 41494834507059872136357493)
                    ·
                      refine ⟨3890140735036863012783515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41494834507059872136357493 3890140735036863012783515)
                      ·
                        rfl

theorem cell23_7576022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7576022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576022 prefixEnd_7576022 := by exact prefixLift 7576022
  have htrace : WordTrace (prefixWord ++ tailWord_7576022) baseStart_7576022 baseEnd_7576022 := by
    simpa [prefixWord, tailWord_7576022, baseEnd_7576022] using wordTrace_append hprefix tailTrace_7576022
  have hstable : (prefixWord ++ tailWord_7576022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576022).length < 2 ^ (prefixWord ++ tailWord_7576022).sum := by decide
  have hdescent : baseEnd_7576022 < baseStart_7576022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576032 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 2, 4, 2]
def baseStart_7576032 : Nat := 118140960795 + 7576032 * 2 ^ 59
def prefixEnd_7576032 : Nat := 4983230072969 + 3 ^ 40 * 7576032 * 2
def baseEnd_7576032 : Nat := 3890145869843407973658469

theorem tailTrace_7576032 : CollatzResearch.WordTrace tailWord_7576032 prefixEnd_7576032 3890145869843407973658469 := by
  unfold tailWord_7576032
  simp only [CollatzResearch.WordTrace]
  refine ⟨138160293844668711049701175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184213725126224948066268233 138160293844668711049701175)
  ·
    refine ⟨207240440767003066574551763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138160293844668711049701175 207240440767003066574551763)
    ·
      refine ⟨310860661150504599861827645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207240440767003066574551763 310860661150504599861827645)
      ·
        refine ⟨116572747931439224948185367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310860661150504599861827645 116572747931439224948185367)
        ·
          refine ⟨174859121897158837422278051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116572747931439224948185367 174859121897158837422278051)
          ·
            refine ⟨262288682845738256133417077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174859121897158837422278051 262288682845738256133417077)
            ·
              refine ⟨24589564016787961512507851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262288682845738256133417077 24589564016787961512507851)
              ·
                refine ⟨36884346025181942268761777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24589564016787961512507851 36884346025181942268761777)
                ·
                  refine ⟨27663259518886456701571333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36884346025181942268761777 27663259518886456701571333)
                  ·
                    refine ⟨5186861159791210631544625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27663259518886456701571333 5186861159791210631544625)
                    ·
                      refine ⟨3890145869843407973658469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5186861159791210631544625 3890145869843407973658469)
                      ·
                        rfl

theorem cell23_7576032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_7576032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576032 prefixEnd_7576032 := by exact prefixLift 7576032
  have htrace : WordTrace (prefixWord ++ tailWord_7576032) baseStart_7576032 baseEnd_7576032 := by
    simpa [prefixWord, tailWord_7576032, baseEnd_7576032] using wordTrace_append hprefix tailTrace_7576032
  have hstable : (prefixWord ++ tailWord_7576032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576032).length < 2 ^ (prefixWord ++ tailWord_7576032).sum := by decide
  have hdescent : baseEnd_7576032 < baseStart_7576032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576042 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_7576042 : Nat := 118140960795 + 7576042 * 2 ^ 59
def prefixEnd_7576042 : Nat := 4983230072969 + 3 ^ 40 * 7576042 * 2
def baseEnd_7576042 : Nat := 1296717001549984311511141

theorem tailTrace_7576042 : CollatzResearch.WordTrace tailWord_7576042 prefixEnd_7576042 1296717001549984311511141 := by
  unfold tailWord_7576042
  simp only [CollatzResearch.WordTrace]
  refine ⟨69080238104825298451816595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184213968279534129204844253 69080238104825298451816595)
  ·
    refine ⟨103620357157237947677724893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69080238104825298451816595 103620357157237947677724893)
    ·
      refine ⟨38857633933964230379146835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103620357157237947677724893 38857633933964230379146835)
      ·
        refine ⟨58286450900946345568720253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38857633933964230379146835 58286450900946345568720253)
        ·
          refine ⟨21857419087854879588270095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58286450900946345568720253 21857419087854879588270095)
          ·
            refine ⟨32786128631782319382405143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21857419087854879588270095 32786128631782319382405143)
            ·
              refine ⟨49179192947673479073607715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32786128631782319382405143 49179192947673479073607715)
              ·
                refine ⟨73768789421510218610411573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49179192947673479073607715 73768789421510218610411573)
                ·
                  refine ⟨6915824008266582994726085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73768789421510218610411573 6915824008266582994726085)
                  ·
                    refine ⟨1296717001549984311511141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6915824008266582994726085 1296717001549984311511141)
                    ·
                      rfl

theorem cell23_7576042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_7576042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576042 prefixEnd_7576042 := by exact prefixLift 7576042
  have htrace : WordTrace (prefixWord ++ tailWord_7576042) baseStart_7576042 baseEnd_7576042 := by
    simpa [prefixWord, tailWord_7576042, baseEnd_7576042] using wordTrace_append hprefix tailTrace_7576042
  have hstable : (prefixWord ++ tailWord_7576042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576042).length < 2 ^ (prefixWord ++ tailWord_7576042).sum := by decide
  have hdescent : baseEnd_7576042 < baseStart_7576042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576075 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 6]
def baseStart_7576075 : Nat := 118140960795 + 7576075 * 2 ^ 59
def prefixEnd_7576075 : Nat := 4983230072969 + 3 ^ 40 * 7576075 * 2
def baseEnd_7576075 : Nat := 3890167949511551305420771

theorem tailTrace_7576075 : CollatzResearch.WordTrace tailWord_7576075 prefixEnd_7576075 3890167949511551305420771 := by
  unfold tailWord_7576075
  simp only [CollatzResearch.WordTrace]
  refine ⟨276322156028181640443217679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184214770685454426962145119 276322156028181640443217679)
  ·
    refine ⟨414483234042272460664826519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276322156028181640443217679 414483234042272460664826519)
    ·
      refine ⟨621724851063408690997239779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414483234042272460664826519 621724851063408690997239779)
      ·
        refine ⟨932587276595113036495859669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621724851063408690997239779 932587276595113036495859669)
        ·
          refine ⟨21857514295197961792871711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 932587276595113036495859669 21857514295197961792871711)
          ·
            refine ⟨32786271442796942689307567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21857514295197961792871711 32786271442796942689307567)
            ·
              refine ⟨49179407164195414033961351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32786271442796942689307567 49179407164195414033961351)
              ·
                refine ⟨73769110746293121050942027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49179407164195414033961351 73769110746293121050942027)
                ·
                  refine ⟨110653666119439681576413041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73769110746293121050942027 110653666119439681576413041)
                  ·
                    refine ⟨82990249589579761182309781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110653666119439681576413041 82990249589579761182309781)
                    ·
                      refine ⟨3890167949511551305420771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82990249589579761182309781 3890167949511551305420771)
                      ·
                        rfl

theorem cell23_7576075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 6].length) (baseStart_7576075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576075 prefixEnd_7576075 := by exact prefixLift 7576075
  have htrace : WordTrace (prefixWord ++ tailWord_7576075) baseStart_7576075 baseEnd_7576075 := by
    simpa [prefixWord, tailWord_7576075, baseEnd_7576075] using wordTrace_append hprefix tailTrace_7576075
  have hstable : (prefixWord ++ tailWord_7576075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576075).length < 2 ^ (prefixWord ++ tailWord_7576075).sum := by decide
  have hdescent : baseEnd_7576075 < baseStart_7576075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576099 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 3]
def baseStart_7576099 : Nat := 118140960795 + 7576099 * 2 ^ 59
def prefixEnd_7576099 : Nat := 4983230072969 + 3 ^ 40 * 7576099 * 2
def baseEnd_7576099 : Nat := 3890180273047259211520661

theorem tailTrace_7576099 : CollatzResearch.WordTrace tailWord_7576099 prefixEnd_7576099 3890180273047259211520661 := by
  unfold tailWord_7576099
  simp only [CollatzResearch.WordTrace]
  refine ⟨276323031380094692542091351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184215354253396461694727567 276323031380094692542091351)
  ·
    refine ⟨414484547070142038813137027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276323031380094692542091351 414484547070142038813137027)
    ·
      refine ⟨621726820605213058219705541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414484547070142038813137027 621726820605213058219705541)
      ·
        refine ⟨116573778863477448416194789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 621726820605213058219705541 116573778863477448416194789)
        ·
          refine ⟨21857583536902021578036523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116573778863477448416194789 21857583536902021578036523)
          ·
            refine ⟨32786375305353032367054785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21857583536902021578036523 32786375305353032367054785)
            ·
              refine ⟨24589781479014774275291089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32786375305353032367054785 24589781479014774275291089)
              ·
                refine ⟨18442336109261080706468317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24589781479014774275291089 18442336109261080706468317)
                ·
                  refine ⟨6915876040972905264925619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18442336109261080706468317 6915876040972905264925619)
                  ·
                    refine ⟨10373814061459357897388429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6915876040972905264925619 10373814061459357897388429)
                    ·
                      refine ⟨3890180273047259211520661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10373814061459357897388429 3890180273047259211520661)
                      ·
                        rfl

theorem cell23_7576099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_7576099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576099 prefixEnd_7576099 := by exact prefixLift 7576099
  have htrace : WordTrace (prefixWord ++ tailWord_7576099) baseStart_7576099 baseEnd_7576099 := by
    simpa [prefixWord, tailWord_7576099, baseEnd_7576099] using wordTrace_append hprefix tailTrace_7576099
  have hstable : (prefixWord ++ tailWord_7576099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576099).length < 2 ^ (prefixWord ++ tailWord_7576099).sum := by decide
  have hdescent : baseEnd_7576099 < baseStart_7576099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576110 : List Nat := [4, 1, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_7576110 : Nat := 118140960795 + 7576110 * 2 ^ 59
def prefixEnd_7576110 : Nat := 4983230072969 + 3 ^ 40 * 7576110 * 2
def baseEnd_7576110 : Nat := 1296728640444819556161037

theorem tailTrace_7576110 : CollatzResearch.WordTrace tailWord_7576110 prefixEnd_7576110 1296728640444819556161037 := by
  unfold tailWord_7576110
  simp only [CollatzResearch.WordTrace]
  refine ⟨34540429072881855177592723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184215621722036560947161189 34540429072881855177592723)
  ·
    refine ⟨51810643609322782766389085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34540429072881855177592723 51810643609322782766389085)
    ·
      refine ⟨19428991353496043537395907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51810643609322782766389085 19428991353496043537395907)
      ·
        refine ⟨29143487030244065306093861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19428991353496043537395907 29143487030244065306093861)
        ·
          refine ⟨5464403818170762244892599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29143487030244065306093861 5464403818170762244892599)
          ·
            refine ⟨8196605727256143367338899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464403818170762244892599 8196605727256143367338899)
            ·
              refine ⟨12294908590884215051008349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196605727256143367338899 12294908590884215051008349)
              ·
                refine ⟨4610590721581580644128131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12294908590884215051008349 4610590721581580644128131)
                ·
                  refine ⟨6915886082372370966192197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610590721581580644128131 6915886082372370966192197)
                  ·
                    refine ⟨1296728640444819556161037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6915886082372370966192197 1296728640444819556161037)
                    ·
                      rfl

theorem cell23_7576110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_7576110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576110 prefixEnd_7576110 := by exact prefixLift 7576110
  have htrace : WordTrace (prefixWord ++ tailWord_7576110) baseStart_7576110 baseEnd_7576110 := by
    simpa [prefixWord, tailWord_7576110, baseEnd_7576110] using wordTrace_append hprefix tailTrace_7576110
  have hstable : (prefixWord ++ tailWord_7576110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576110).length < 2 ^ (prefixWord ++ tailWord_7576110).sum := by decide
  have hdescent : baseEnd_7576110 < baseStart_7576110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576115 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 3, 6]
def baseStart_7576115 : Nat := 118140960795 + 7576115 * 2 ^ 59
def prefixEnd_7576115 : Nat := 4983230072969 + 3 ^ 40 * 7576115 * 2
def baseEnd_7576115 : Nat := 1296729496245910382973529

theorem tailTrace_7576115 : CollatzResearch.WordTrace tailWord_7576115 prefixEnd_7576115 1296729496245910382973529 := by
  unfold tailWord_7576115
  simp only [CollatzResearch.WordTrace]
  refine ⟨276323614948036727274673799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184215743298691151516449199 276323614948036727274673799)
  ·
    refine ⟨414485422422055090912010699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276323614948036727274673799 414485422422055090912010699)
    ·
      refine ⟨621728133633082636368016049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414485422422055090912010699 621728133633082636368016049)
      ·
        refine ⟨466296100224811977276012037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621728133633082636368016049 466296100224811977276012037)
        ·
          refine ⟨87430518792152245739252257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466296100224811977276012037 87430518792152245739252257)
          ·
            refine ⟨65572889094114184304439193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87430518792152245739252257 65572889094114184304439193)
            ·
              refine ⟨49179666820585638228329395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65572889094114184304439193 49179666820585638228329395)
              ·
                refine ⟨73769500230878457342494093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49179666820585638228329395 73769500230878457342494093)
                ·
                  refine ⟨27663562586579421503435285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73769500230878457342494093 27663562586579421503435285)
                  ·
                    refine ⟨1296729496245910382973529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27663562586579421503435285 1296729496245910382973529)
                    ·
                      rfl

theorem cell23_7576115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 6].length) (baseStart_7576115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576115 prefixEnd_7576115 := by exact prefixLift 7576115
  have htrace : WordTrace (prefixWord ++ tailWord_7576115) baseStart_7576115 baseEnd_7576115 := by
    simpa [prefixWord, tailWord_7576115, baseEnd_7576115] using wordTrace_append hprefix tailTrace_7576115
  have hstable : (prefixWord ++ tailWord_7576115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576115).length < 2 ^ (prefixWord ++ tailWord_7576115).sum := by decide
  have hdescent : baseEnd_7576115 < baseStart_7576115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576133 : List Nat := [1, 3, 1, 1, 1, 6, 3, 2, 1, 1, 3]
def baseStart_7576133 : Nat := 118140960795 + 7576133 * 2 ^ 59
def prefixEnd_7576133 : Nat := 4983230072969 + 3 ^ 40 * 7576133 * 2
def baseEnd_7576133 : Nat := 3890197731389512078495505

theorem tailTrace_7576133 : CollatzResearch.WordTrace tailWord_7576133 prefixEnd_7576133 3890197731389512078495505 := by
  unfold tailWord_7576133
  simp only [CollatzResearch.WordTrace]
  refine ⟨276324271461971516348829053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184216180974647677565886035 276324271461971516348829053)
  ·
    refine ⟨103621601798239318630810895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276324271461971516348829053 103621601798239318630810895)
    ·
      refine ⟨155432402697358977946216343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103621601798239318630810895 155432402697358977946216343)
      ·
        refine ⟨233148604046038466919324515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155432402697358977946216343 233148604046038466919324515)
        ·
          refine ⟨349722906069057700378986773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233148604046038466919324515 349722906069057700378986773)
          ·
            refine ⟨16393261221987079705265005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 349722906069057700378986773 16393261221987079705265005)
            ·
              refine ⟨6147472958245154889474377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16393261221987079705265005 6147472958245154889474377)
              ·
                refine ⟨4610604718683866167105783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6147472958245154889474377 4610604718683866167105783)
                ·
                  refine ⟨6915907078025799250658675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610604718683866167105783 6915907078025799250658675)
                  ·
                    refine ⟨10373860617038698875988013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6915907078025799250658675 10373860617038698875988013)
                    ·
                      refine ⟨3890197731389512078495505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10373860617038698875988013 3890197731389512078495505)
                      ·
                        rfl

theorem cell23_7576133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_7576133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576133 prefixEnd_7576133 := by exact prefixLift 7576133
  have htrace : WordTrace (prefixWord ++ tailWord_7576133) baseStart_7576133 baseEnd_7576133 := by
    simpa [prefixWord, tailWord_7576133, baseEnd_7576133] using wordTrace_append hprefix tailTrace_7576133
  have hstable : (prefixWord ++ tailWord_7576133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576133).length < 2 ^ (prefixWord ++ tailWord_7576133).sum := by decide
  have hdescent : baseEnd_7576133 < baseStart_7576133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576142 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_7576142 : Nat := 118140960795 + 7576142 * 2 ^ 59
def prefixEnd_7576142 : Nat := 4983230072969 + 3 ^ 40 * 7576142 * 2
def baseEnd_7576142 : Nat := 3890202352715402543282963

theorem tailTrace_7576142 : CollatzResearch.WordTrace tailWord_7576142 prefixEnd_7576142 3890202352715402543282963 := by
  unfold tailWord_7576142
  simp only [CollatzResearch.WordTrace]
  refine ⟨34540574964867363860738335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184216399812625940590604453 34540574964867363860738335)
  ·
    refine ⟨51810862447301045791107503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34540574964867363860738335 51810862447301045791107503)
    ·
      refine ⟨77716293670951568686661255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51810862447301045791107503 77716293670951568686661255)
      ·
        refine ⟨116574440506427353029991883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77716293670951568686661255 116574440506427353029991883)
        ·
          refine ⟨174861660759641029544987825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116574440506427353029991883 174861660759641029544987825)
          ·
            refine ⟨131146245569730772158740869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174861660759641029544987825 131146245569730772158740869)
            ·
              refine ⟨24589921044324519779763913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131146245569730772158740869 24589921044324519779763913)
              ·
                refine ⟨18442440783243389834822935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24589921044324519779763913 18442440783243389834822935)
                ·
                  refine ⟨27663661174865084752234403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18442440783243389834822935 27663661174865084752234403)
                  ·
                    refine ⟨41495491762297627128351605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27663661174865084752234403 41495491762297627128351605)
                    ·
                      refine ⟨3890202352715402543282963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41495491762297627128351605 3890202352715402543282963)
                      ·
                        rfl

theorem cell23_7576142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_7576142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576142 prefixEnd_7576142 := by exact prefixLift 7576142
  have htrace : WordTrace (prefixWord ++ tailWord_7576142) baseStart_7576142 baseEnd_7576142 := by
    simpa [prefixWord, tailWord_7576142, baseEnd_7576142] using wordTrace_append hprefix tailTrace_7576142
  have hstable : (prefixWord ++ tailWord_7576142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576142).length < 2 ^ (prefixWord ++ tailWord_7576142).sum := by decide
  have hdescent : baseEnd_7576142 < baseStart_7576142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576145 : List Nat := [1, 2, 2, 1, 3, 3, 1, 10]
def baseStart_7576145 : Nat := 118140960795 + 7576145 * 2 ^ 59
def prefixEnd_7576145 : Nat := 4983230072969 + 3 ^ 40 * 7576145 * 2
def baseEnd_7576145 : Nat := 144081625672495038205387

theorem tailTrace_7576145 : CollatzResearch.WordTrace tailWord_7576145 prefixEnd_7576145 144081625672495038205387 := by
  unfold tailWord_7576145
  simp only [CollatzResearch.WordTrace]
  refine ⟨276324709137928042398265889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184216472758618694932177259 276324709137928042398265889)
  ·
    refine ⟨207243531853446031798699417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276324709137928042398265889 207243531853446031798699417)
    ·
      refine ⟨155432648890084523849024563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207243531853446031798699417 155432648890084523849024563)
      ·
        refine ⟨233148973335126785773536845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155432648890084523849024563 233148973335126785773536845)
        ·
          refine ⟨87430865000672544665076317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233148973335126785773536845 87430865000672544665076317)
          ·
            refine ⟨32786574375252204249403619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87430865000672544665076317 32786574375252204249403619)
            ·
              refine ⟨49179861562878306374105429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32786574375252204249403619 49179861562878306374105429)
              ·
                refine ⟨144081625672495038205387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49179861562878306374105429 144081625672495038205387)
                ·
                  rfl

theorem cell23_7576145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 10].length) (baseStart_7576145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576145 prefixEnd_7576145 := by exact prefixLift 7576145
  have htrace : WordTrace (prefixWord ++ tailWord_7576145) baseStart_7576145 baseEnd_7576145 := by
    simpa [prefixWord, tailWord_7576145, baseEnd_7576145] using wordTrace_append hprefix tailTrace_7576145
  have hstable : (prefixWord ++ tailWord_7576145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576145).length < 2 ^ (prefixWord ++ tailWord_7576145).sum := by decide
  have hdescent : baseEnd_7576145 < baseStart_7576145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576172 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 3]
def baseStart_7576172 : Nat := 118140960795 + 7576172 * 2 ^ 59
def prefixEnd_7576172 : Nat := 4983230072969 + 3 ^ 40 * 7576172 * 2
def baseEnd_7576172 : Nat := 3890217757135037425907825

theorem tailTrace_7576172 : CollatzResearch.WordTrace tailWord_7576172 prefixEnd_7576172 3890217757135037425907825 := by
  unfold tailWord_7576172
  simp only [CollatzResearch.WordTrace]
  refine ⟨138162846954415113004749385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184217129272553484006332513 138162846954415113004749385)
  ·
    refine ⟨103622135215811334753562039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138162846954415113004749385 103622135215811334753562039)
    ·
      refine ⟨155433202823717002130343059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103622135215811334753562039 155433202823717002130343059)
      ·
        refine ⟨233149804235575503195514589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155433202823717002130343059 233149804235575503195514589)
        ·
          refine ⟨87431176588340813698317971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233149804235575503195514589 87431176588340813698317971)
          ·
            refine ⟨131146764882511220547476957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87431176588340813698317971 131146764882511220547476957)
            ·
              refine ⟨49180036830941707705303859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131146764882511220547476957 49180036830941707705303859)
              ·
                refine ⟨73770055246412561557955789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49180036830941707705303859 73770055246412561557955789)
                ·
                  refine ⟨27663770717404710584233421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73770055246412561557955789 27663770717404710584233421)
                  ·
                    refine ⟨10373914019026766469087533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27663770717404710584233421 10373914019026766469087533)
                    ·
                      refine ⟨3890217757135037425907825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10373914019026766469087533 3890217757135037425907825)
                      ·
                        rfl

theorem cell23_7576172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_7576172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576172 prefixEnd_7576172 := by exact prefixLift 7576172
  have htrace : WordTrace (prefixWord ++ tailWord_7576172) baseStart_7576172 baseEnd_7576172 := by
    simpa [prefixWord, tailWord_7576172, baseEnd_7576172] using wordTrace_append hprefix tailTrace_7576172
  have hstable : (prefixWord ++ tailWord_7576172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576172).length < 2 ^ (prefixWord ++ tailWord_7576172).sum := by decide
  have hdescent : baseEnd_7576172 < baseStart_7576172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576176 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 1, 1, 5]
def baseStart_7576176 : Nat := 118140960795 + 7576176 * 2 ^ 59
def prefixEnd_7576176 : Nat := 4983230072969 + 3 ^ 40 * 7576176 * 2
def baseEnd_7576176 : Nat := 3890219811057655410257807

theorem tailTrace_7576176 : CollatzResearch.WordTrace tailWord_7576176 prefixEnd_7576176 3890219811057655410257807 := by
  unfold tailWord_7576176
  simp only [CollatzResearch.WordTrace]
  refine ⟨138162919900407867346322191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184217226533877156461762921 138162919900407867346322191)
  ·
    refine ⟨207244379850611801019483287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138162919900407867346322191 207244379850611801019483287)
    ·
      refine ⟨310866569775917701529224931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207244379850611801019483287 310866569775917701529224931)
      ·
        refine ⟨466299854663876552293837397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310866569775917701529224931 466299854663876552293837397)
        ·
          refine ⟨5464451421842303347193407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 466299854663876552293837397 5464451421842303347193407)
          ·
            refine ⟨8196677132763455020790111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464451421842303347193407 8196677132763455020790111)
            ·
              refine ⟨12295015699145182531185167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8196677132763455020790111 12295015699145182531185167)
              ·
                refine ⟨18442523548717773796777751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12295015699145182531185167 18442523548717773796777751)
                ·
                  refine ⟨27663785323076660695166627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18442523548717773796777751 27663785323076660695166627)
                  ·
                    refine ⟨41495677984614991042749941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27663785323076660695166627 41495677984614991042749941)
                    ·
                      refine ⟨3890219811057655410257807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41495677984614991042749941 3890219811057655410257807)
                      ·
                        rfl

theorem cell23_7576176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 1, 5].length) (baseStart_7576176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576176 prefixEnd_7576176 := by exact prefixLift 7576176
  have htrace : WordTrace (prefixWord ++ tailWord_7576176) baseStart_7576176 baseEnd_7576176 := by
    simpa [prefixWord, tailWord_7576176, baseEnd_7576176] using wordTrace_append hprefix tailTrace_7576176
  have hstable : (prefixWord ++ tailWord_7576176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576176).length < 2 ^ (prefixWord ++ tailWord_7576176).sum := by decide
  have hdescent : baseEnd_7576176 < baseStart_7576176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576199 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_7576199 : Nat := 118140960795 + 7576199 * 2 ^ 59
def prefixEnd_7576199 : Nat := 4983230072969 + 3 ^ 40 * 7576199 * 2
def baseEnd_7576199 : Nat := 3890231621112708820270201

theorem tailTrace_7576199 : CollatzResearch.WordTrace tailWord_7576199 prefixEnd_7576199 3890231621112708820270201 := by
  unfold tailWord_7576199
  simp only [CollatzResearch.WordTrace]
  refine ⟨276326678679732409620731651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184217785786488273080487767 276326678679732409620731651)
  ·
    refine ⟨414490018019598614431097477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276326678679732409620731651 414490018019598614431097477)
    ·
      refine ⟨77716878378674740205830777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 414490018019598614431097477 77716878378674740205830777)
      ·
        refine ⟨58287658784006055154373083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77716878378674740205830777 58287658784006055154373083)
        ·
          refine ⟨87431488176009082731559625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58287658784006055154373083 87431488176009082731559625)
          ·
            refine ⟨65573616132006812048669719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87431488176009082731559625 65573616132006812048669719)
            ·
              refine ⟨98360424198010218073004579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65573616132006812048669719 98360424198010218073004579)
              ·
                refine ⟨147540636297015327109506869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98360424198010218073004579 147540636297015327109506869)
                ·
                  refine ⟨13831934652845186916516269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147540636297015327109506869 13831934652845186916516269)
                  ·
                    refine ⟨5186975494816945093693601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13831934652845186916516269 5186975494816945093693601)
                    ·
                      refine ⟨3890231621112708820270201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5186975494816945093693601 3890231621112708820270201)
                      ·
                        rfl

theorem cell23_7576199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_7576199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576199 prefixEnd_7576199 := by exact prefixLift 7576199
  have htrace : WordTrace (prefixWord ++ tailWord_7576199) baseStart_7576199 baseEnd_7576199 := by
    simpa [prefixWord, tailWord_7576199, baseEnd_7576199] using wordTrace_append hprefix tailTrace_7576199
  have hstable : (prefixWord ++ tailWord_7576199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576199).length < 2 ^ (prefixWord ++ tailWord_7576199).sum := by decide
  have hdescent : baseEnd_7576199 < baseStart_7576199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576206 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_7576206 : Nat := 118140960795 + 7576206 * 2 ^ 59
def prefixEnd_7576206 : Nat := 4983230072969 + 3 ^ 40 * 7576206 * 2
def baseEnd_7576206 : Nat := 3890235215477290292882669

theorem tailTrace_7576206 : CollatzResearch.WordTrace tailWord_7576206 prefixEnd_7576206 3890235215477290292882669 := by
  unfold tailWord_7576206
  simp only [CollatzResearch.WordTrace]
  refine ⟨34540866748838381227029559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184217955993804699877490981 34540866748838381227029559)
  ·
    refine ⟨51811300123257571840544339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34540866748838381227029559 51811300123257571840544339)
    ·
      refine ⟨77716950184886357760816509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51811300123257571840544339 77716950184886357760816509)
      ·
        refine ⟨29143856319332384160306191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77716950184886357760816509 29143856319332384160306191)
        ·
          refine ⟨43715784478998576240459287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29143856319332384160306191 43715784478998576240459287)
          ·
            refine ⟨65573676718497864360688931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43715784478998576240459287 65573676718497864360688931)
            ·
              refine ⟨98360515077746796541033397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65573676718497864360688931 98360515077746796541033397)
              ·
                refine ⟨9221298288538762175721881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98360515077746796541033397 9221298288538762175721881)
                ·
                  refine ⟨6915973716404071631791411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9221298288538762175721881 6915973716404071631791411)
                  ·
                    refine ⟨10373960574606107447687117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6915973716404071631791411 10373960574606107447687117)
                    ·
                      refine ⟨3890235215477290292882669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10373960574606107447687117 3890235215477290292882669)
                      ·
                        rfl

theorem cell23_7576206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_7576206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576206 prefixEnd_7576206 := by exact prefixLift 7576206
  have htrace : WordTrace (prefixWord ++ tailWord_7576206) baseStart_7576206 baseEnd_7576206 := by
    simpa [prefixWord, tailWord_7576206, baseEnd_7576206] using wordTrace_append hprefix tailTrace_7576206
  have hstable : (prefixWord ++ tailWord_7576206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576206).length < 2 ^ (prefixWord ++ tailWord_7576206).sum := by decide
  have hdescent : baseEnd_7576206 < baseStart_7576206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576216 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 1, 3, 2]
def baseStart_7576216 : Nat := 118140960795 + 7576216 * 2 ^ 59
def prefixEnd_7576216 : Nat := 4983230072969 + 3 ^ 40 * 7576216 * 2
def baseEnd_7576216 : Nat := 3890240350283835253757623

theorem tailTrace_7576216 : CollatzResearch.WordTrace tailWord_7576216 prefixEnd_7576216 3890240350283835253757623 := by
  unfold tailWord_7576216
  simp only [CollatzResearch.WordTrace]
  refine ⟨138163649360335410762050251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184218199147113881016067001 138163649360335410762050251)
  ·
    refine ⟨207245474040503116143075377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138163649360335410762050251 207245474040503116143075377)
    ·
      refine ⟨155434105530377337107306533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207245474040503116143075377 155434105530377337107306533)
      ·
        refine ⟨29143894786945750707619975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155434105530377337107306533 29143894786945750707619975)
        ·
          refine ⟨43715842180418626061429963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29143894786945750707619975 43715842180418626061429963)
          ·
            refine ⟨65573763270627939092144945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43715842180418626061429963 65573763270627939092144945)
            ·
              refine ⟨49180322452970954319108709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65573763270627939092144945 49180322452970954319108709)
              ·
                refine ⟨9221310459932053934832883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49180322452970954319108709 9221310459932053934832883)
                ·
                  refine ⟨13831965689898080902249325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9221310459932053934832883 13831965689898080902249325)
                  ·
                    refine ⟨5186987133711780338343497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13831965689898080902249325 5186987133711780338343497)
                    ·
                      refine ⟨3890240350283835253757623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5186987133711780338343497 3890240350283835253757623)
                      ·
                        rfl

theorem cell23_7576216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_7576216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576216 prefixEnd_7576216 := by exact prefixLift 7576216
  have htrace : WordTrace (prefixWord ++ tailWord_7576216) baseStart_7576216 baseEnd_7576216 := by
    simpa [prefixWord, tailWord_7576216, baseEnd_7576216] using wordTrace_append hprefix tailTrace_7576216
  have hstable : (prefixWord ++ tailWord_7576216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576216).length < 2 ^ (prefixWord ++ tailWord_7576216).sum := by decide
  have hdescent : baseEnd_7576216 < baseStart_7576216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576257 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7576257 : Nat := 118140960795 + 7576257 * 2 ^ 59
def prefixEnd_7576257 : Nat := 4983230072969 + 3 ^ 40 * 7576257 * 2
def baseEnd_7576257 : Nat := 3890261402990669593344935

theorem tailTrace_7576257 : CollatzResearch.WordTrace tailWord_7576257 prefixEnd_7576257 3890261402990669593344935 := by
  unfold tailWord_7576257
  simp only [CollatzResearch.WordTrace]
  refine ⟨276328794113522285526343025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184219196075681523684228683 276328794113522285526343025)
  ·
    refine ⟨207246595585141714144757269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276328794113522285526343025 207246595585141714144757269)
    ·
      refine ⟨9714684168053517850535497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 207246595585141714144757269 9714684168053517850535497)
      ·
        refine ⟨7286013126040138387901623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9714684168053517850535497 7286013126040138387901623)
        ·
          refine ⟨10929019689060207581852435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7286013126040138387901623 10929019689060207581852435)
          ·
            refine ⟨16393529533590311372778653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929019689060207581852435 16393529533590311372778653)
            ·
              refine ⟨6147573575096366764791995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16393529533590311372778653 6147573575096366764791995)
              ·
                refine ⟨9221360362644550147187993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6147573575096366764791995 9221360362644550147187993)
                ·
                  refine ⟨6916020271983412610390995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9221360362644550147187993 6916020271983412610390995)
                  ·
                    refine ⟨10374030407975118915586493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6916020271983412610390995 10374030407975118915586493)
                    ·
                      refine ⟨3890261402990669593344935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10374030407975118915586493 3890261402990669593344935)
                      ·
                        rfl

theorem cell23_7576257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7576257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576257 prefixEnd_7576257 := by exact prefixLift 7576257
  have htrace : WordTrace (prefixWord ++ tailWord_7576257) baseStart_7576257 baseEnd_7576257 := by
    simpa [prefixWord, tailWord_7576257, baseEnd_7576257] using wordTrace_append hprefix tailTrace_7576257
  have hstable : (prefixWord ++ tailWord_7576257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576257).length < 2 ^ (prefixWord ++ tailWord_7576257).sum := by decide
  have hdescent : baseEnd_7576257 < baseStart_7576257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576282 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_7576282 : Nat := 118140960795 + 7576282 * 2 ^ 59
def prefixEnd_7576282 : Nat := 4983230072969 + 3 ^ 40 * 7576282 * 2
def baseEnd_7576282 : Nat := 1296758080002343998510773

theorem tailTrace_7576282 : CollatzResearch.WordTrace tailWord_7576282 prefixEnd_7576282 1296758080002343998510773 := by
  unfold tailWord_7576282
  simp only [CollatzResearch.WordTrace]
  refine ⟨69082426484607928699000775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184219803958954476530668733 69082426484607928699000775)
  ·
    refine ⟨103623639726911893048501163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69082426484607928699000775 103623639726911893048501163)
    ·
      refine ⟨155435459590367839572751745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103623639726911893048501163 155435459590367839572751745)
      ·
        refine ⟨116576594692775879679563809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155435459590367839572751745 116576594692775879679563809)
        ·
          refine ⟨87432446019581909759672857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116576594692775879679563809 87432446019581909759672857)
          ·
            refine ⟨65574334514686432319754643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87432446019581909759672857 65574334514686432319754643)
            ·
              refine ⟨98361501772029648479631965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65574334514686432319754643 98361501772029648479631965)
              ·
                refine ⟨36885563164511118179861987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98361501772029648479631965 36885563164511118179861987)
                ·
                  refine ⟨55328344746766677269792981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36885563164511118179861987 55328344746766677269792981)
                  ·
                    refine ⟨1296758080002343998510773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55328344746766677269792981 1296758080002343998510773)
                    ·
                      rfl

theorem cell23_7576282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_7576282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576282 prefixEnd_7576282 := by exact prefixLift 7576282
  have htrace : WordTrace (prefixWord ++ tailWord_7576282) baseStart_7576282 baseEnd_7576282 := by
    simpa [prefixWord, tailWord_7576282, baseEnd_7576282] using wordTrace_append hprefix tailTrace_7576282
  have hstable : (prefixWord ++ tailWord_7576282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576282).length < 2 ^ (prefixWord ++ tailWord_7576282).sum := by decide
  have hdescent : baseEnd_7576282 < baseStart_7576282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576319 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 1, 6, 2]
def baseStart_7576319 : Nat := 118140960795 + 7576319 * 2 ^ 59
def prefixEnd_7576319 : Nat := 4983230072969 + 3 ^ 40 * 7576319 * 2
def baseEnd_7576319 : Nat := 3890293238791248350769649

theorem tailTrace_7576319 : CollatzResearch.WordTrace tailWord_7576319 prefixEnd_7576319 3890293238791248350769649 := by
  unfold tailWord_7576319
  simp only [CollatzResearch.WordTrace]
  refine ⟨276331055439297670115100011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184220703626198446743400007 276331055439297670115100011)
  ·
    refine ⟨414496583158946505172650017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276331055439297670115100011 414496583158946505172650017)
    ·
      refine ⟨310872437369209878879487513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414496583158946505172650017 310872437369209878879487513)
      ·
        refine ⟨233154328026907409159615635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310872437369209878879487513 233154328026907409159615635)
        ·
          refine ⟨349731492040361113739423453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233154328026907409159615635 349731492040361113739423453)
          ·
            refine ⟨131149309515135417652283795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349731492040361113739423453 131149309515135417652283795)
            ·
              refine ⟨196723964272703126478425693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131149309515135417652283795 196723964272703126478425693)
              ·
                refine ⟨73771486602263672429409635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196723964272703126478425693 73771486602263672429409635)
                ·
                  refine ⟨110657229903395508644114453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73771486602263672429409635 110657229903395508644114453)
                  ·
                    refine ⟨5187057651721664467692865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110657229903395508644114453 5187057651721664467692865)
                    ·
                      refine ⟨3890293238791248350769649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5187057651721664467692865 3890293238791248350769649)
                      ·
                        rfl

theorem cell23_7576319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_7576319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576319 prefixEnd_7576319 := by exact prefixLift 7576319
  have htrace : WordTrace (prefixWord ++ tailWord_7576319) baseStart_7576319 baseEnd_7576319 := by
    simpa [prefixWord, tailWord_7576319, baseEnd_7576319] using wordTrace_append hprefix tailTrace_7576319
  have hstable : (prefixWord ++ tailWord_7576319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576319).length < 2 ^ (prefixWord ++ tailWord_7576319).sum := by decide
  have hdescent : baseEnd_7576319 < baseStart_7576319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576329 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 3, 4]
def baseStart_7576329 : Nat := 118140960795 + 7576329 * 2 ^ 59
def prefixEnd_7576329 : Nat := 4983230072969 + 3 ^ 40 * 7576329 * 2
def baseEnd_7576329 : Nat := 1296766124532597770548201

theorem tailTrace_7576329 : CollatzResearch.WordTrace tailWord_7576329 prefixEnd_7576329 1296766124532597770548201 := by
  unfold tailWord_7576329
  simp only [CollatzResearch.WordTrace]
  refine ⟨276331420169261441822964041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184220946779507627881976027 276331420169261441822964041)
  ·
    refine ⟨207248565126946081367223031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276331420169261441822964041 207248565126946081367223031)
    ·
      refine ⟨310872847690419122050834547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207248565126946081367223031 310872847690419122050834547)
      ·
        refine ⟨466309271535628683076251821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310872847690419122050834547 466309271535628683076251821)
        ·
          refine ⟨174865976825860756153594433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466309271535628683076251821 174865976825860756153594433)
          ·
            refine ⟨131149482619395567115195825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174865976825860756153594433 131149482619395567115195825)
            ·
              refine ⟨98362111964546675336396869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131149482619395567115195825 98362111964546675336396869)
              ·
                refine ⟨18442895993352501625574413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98362111964546675336396869 18442895993352501625574413)
                ·
                  refine ⟨6916085997507188109590405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18442895993352501625574413 6916085997507188109590405)
                  ·
                    refine ⟨1296766124532597770548201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916085997507188109590405 1296766124532597770548201)
                    ·
                      rfl

theorem cell23_7576329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 4].length) (baseStart_7576329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576329 prefixEnd_7576329 := by exact prefixLift 7576329
  have htrace : WordTrace (prefixWord ++ tailWord_7576329) baseStart_7576329 baseEnd_7576329 := by
    simpa [prefixWord, tailWord_7576329, baseEnd_7576329] using wordTrace_append hprefix tailTrace_7576329
  have hstable : (prefixWord ++ tailWord_7576329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576329).length < 2 ^ (prefixWord ++ tailWord_7576329).sum := by decide
  have hdescent : baseEnd_7576329 < baseStart_7576329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576332 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_7576332 : Nat := 118140960795 + 7576332 * 2 ^ 59
def prefixEnd_7576332 : Nat := 4983230072969 + 3 ^ 40 * 7576332 * 2
def baseEnd_7576332 : Nat := 3890299914039756799907089

theorem tailTrace_7576332 : CollatzResearch.WordTrace tailWord_7576332 prefixEnd_7576332 3890299914039756799907089 := by
  unfold tailWord_7576332
  simp only [CollatzResearch.WordTrace]
  refine ⟨138165764794125286667661625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184221019725500382223548833 138165764794125286667661625)
  ·
    refine ⟨103624323595593965000746219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138165764794125286667661625 103624323595593965000746219)
    ·
      refine ⟨155436485393390947501119329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103624323595593965000746219 155436485393390947501119329)
      ·
        refine ⟨116577364045043210625839497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155436485393390947501119329 116577364045043210625839497)
        ·
          refine ⟨87433023033782407969379623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116577364045043210625839497 87433023033782407969379623)
          ·
            refine ⟨131149534550673611954069435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87433023033782407969379623 131149534550673611954069435)
            ·
              refine ⟨196724301826010417931104153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131149534550673611954069435 196724301826010417931104153)
              ·
                refine ⟨147543226369507813448328115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196724301826010417931104153 147543226369507813448328115)
                ·
                  refine ⟨221314839554261720172492173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147543226369507813448328115 221314839554261720172492173)
                  ·
                    refine ⟨82993064832848145064684565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221314839554261720172492173 82993064832848145064684565)
                    ·
                      refine ⟨3890299914039756799907089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82993064832848145064684565 3890299914039756799907089)
                      ·
                        rfl

theorem cell23_7576332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_7576332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576332 prefixEnd_7576332 := by exact prefixLift 7576332
  have htrace : WordTrace (prefixWord ++ tailWord_7576332) baseStart_7576332 baseEnd_7576332 := by
    simpa [prefixWord, tailWord_7576332, baseEnd_7576332] using wordTrace_append hprefix tailTrace_7576332
  have hstable : (prefixWord ++ tailWord_7576332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576332).length < 2 ^ (prefixWord ++ tailWord_7576332).sum := by decide
  have hdescent : baseEnd_7576332 < baseStart_7576332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576390 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7576390 : Nat := 118140960795 + 7576390 * 2 ^ 59
def prefixEnd_7576390 : Nat := 4983230072969 + 3 ^ 40 * 7576390 * 2
def baseEnd_7576390 : Nat := 3890329695917717572981823

theorem tailTrace_7576390 : CollatzResearch.WordTrace tailWord_7576390 prefixEnd_7576390 3890329695917717572981823 := by
  unfold tailWord_7576390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635426406938764038779207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184222430014693632827289749 8635426406938764038779207)
  ·
    refine ⟨12953139610408146058168811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8635426406938764038779207 12953139610408146058168811)
    ·
      refine ⟨19429709415612219087253217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953139610408146058168811 19429709415612219087253217)
      ·
        refine ⟨14572282061709164315439913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19429709415612219087253217 14572282061709164315439913)
        ·
          refine ⟨10929211546281873236579935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14572282061709164315439913 10929211546281873236579935)
          ·
            refine ⟨16393817319422809854869903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929211546281873236579935 16393817319422809854869903)
            ·
              refine ⟨24590725979134214782304855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16393817319422809854869903 24590725979134214782304855)
              ·
                refine ⟨36886088968701322173457283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24590725979134214782304855 36886088968701322173457283)
                ·
                  refine ⟨55329133453051983260185925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36886088968701322173457283 55329133453051983260185925)
                  ·
                    refine ⟨10374212522447246861284861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55329133453051983260185925 10374212522447246861284861)
                    ·
                      refine ⟨3890329695917717572981823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10374212522447246861284861 3890329695917717572981823)
                      ·
                        rfl

theorem cell23_7576390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7576390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576390 prefixEnd_7576390 := by exact prefixLift 7576390
  have htrace : WordTrace (prefixWord ++ tailWord_7576390) baseStart_7576390 baseEnd_7576390 := by
    simpa [prefixWord, tailWord_7576390, baseEnd_7576390] using wordTrace_append hprefix tailTrace_7576390
  have hstable : (prefixWord ++ tailWord_7576390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576390).length < 2 ^ (prefixWord ++ tailWord_7576390).sum := by decide
  have hdescent : baseEnd_7576390 < baseStart_7576390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576397 : List Nat := [1, 6, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_7576397 : Nat := 118140960795 + 7576397 * 2 ^ 59
def prefixEnd_7576397 : Nat := 4983230072969 + 3 ^ 40 * 7576397 * 2
def baseEnd_7576397 : Nat := 1296777763427433015198097

theorem tailTrace_7576397 : CollatzResearch.WordTrace tailWord_7576397 prefixEnd_7576397 1296777763427433015198097 := by
  unfold tailWord_7576397
  simp only [CollatzResearch.WordTrace]
  refine ⟨276333900333015089436439445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184222600222010059624292963 276333900333015089436439445)
  ·
    refine ⟨12953151578110082317333099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 276333900333015089436439445 12953151578110082317333099)
    ·
      refine ⟨19429727367165123475999649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953151578110082317333099 19429727367165123475999649)
      ·
        refine ⟨14572295525373842606999737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19429727367165123475999649 14572295525373842606999737)
        ·
          refine ⟨10929221644030381955249803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14572295525373842606999737 10929221644030381955249803)
          ·
            refine ⟨16393832466045572932874705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929221644030381955249803 16393832466045572932874705)
            ·
              refine ⟨12295374349534179699656029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16393832466045572932874705 12295374349534179699656029)
              ·
                refine ⟨4610765381075317387371011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12295374349534179699656029 4610765381075317387371011)
                ·
                  refine ⟨6916148071612976081056517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610765381075317387371011 6916148071612976081056517)
                  ·
                    refine ⟨1296777763427433015198097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916148071612976081056517 1296777763427433015198097)
                    ·
                      rfl

theorem cell23_7576397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_7576397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576397 prefixEnd_7576397 := by exact prefixLift 7576397
  have htrace : WordTrace (prefixWord ++ tailWord_7576397) baseStart_7576397 baseEnd_7576397 := by
    simpa [prefixWord, tailWord_7576397, baseEnd_7576397] using wordTrace_append hprefix tailTrace_7576397
  have hstable : (prefixWord ++ tailWord_7576397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576397).length < 2 ^ (prefixWord ++ tailWord_7576397).sum := by decide
  have hdescent : baseEnd_7576397 < baseStart_7576397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576420 : List Nat := [2, 3, 1, 1, 4, 1, 2, 4, 1, 1, 3]
def baseStart_7576420 : Nat := 118140960795 + 7576420 * 2 ^ 59
def prefixEnd_7576420 : Nat := 4983230072969 + 3 ^ 40 * 7576420 * 2
def baseEnd_7576420 : Nat := 3890345100337352455606685

theorem tailTrace_7576420 : CollatzResearch.WordTrace tailWord_7576420 prefixEnd_7576420 3890345100337352455606685 := by
  unfold tailWord_7576420
  simp only [CollatzResearch.WordTrace]
  refine ⟨138167369605965882182263357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184223159474621176243017809 138167369605965882182263357)
  ·
    refine ⟨51812763602237205818348759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138167369605965882182263357 51812763602237205818348759)
    ·
      refine ⟨77719145403355808727523139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51812763602237205818348759 77719145403355808727523139)
      ·
        refine ⟨116578718105033713091284709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77719145403355808727523139 116578718105033713091284709)
        ·
          refine ⟨21858509644693821204615883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116578718105033713091284709 21858509644693821204615883)
          ·
            refine ⟨32787764467040731806923825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21858509644693821204615883 32787764467040731806923825)
            ·
              refine ⟨24590823350280548855192869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32787764467040731806923825 24590823350280548855192869)
              ·
                refine ⟨4610779378177602910348663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24590823350280548855192869 4610779378177602910348663)
                ·
                  refine ⟨6916169067266404365522995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610779378177602910348663 6916169067266404365522995)
                  ·
                    refine ⟨10374253600899606548284493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6916169067266404365522995 10374253600899606548284493)
                    ·
                      refine ⟨3890345100337352455606685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10374253600899606548284493 3890345100337352455606685)
                      ·
                        rfl

theorem cell23_7576420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_7576420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576420 prefixEnd_7576420 := by exact prefixLift 7576420
  have htrace : WordTrace (prefixWord ++ tailWord_7576420) baseStart_7576420 baseEnd_7576420 := by
    simpa [prefixWord, tailWord_7576420, baseEnd_7576420] using wordTrace_append hprefix tailTrace_7576420
  have hstable : (prefixWord ++ tailWord_7576420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576420).length < 2 ^ (prefixWord ++ tailWord_7576420).sum := by decide
  have hdescent : baseEnd_7576420 < baseStart_7576420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576443 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 3, 2, 2]
def baseStart_7576443 : Nat := 118140960795 + 7576443 * 2 ^ 59
def prefixEnd_7576443 : Nat := 4983230072969 + 3 ^ 40 * 7576443 * 2
def baseEnd_7576443 : Nat := 3890356910392405865619079

theorem tailTrace_7576443 : CollatzResearch.WordTrace tailWord_7576443 prefixEnd_7576443 3890356910392405865619079 := by
  unfold tailWord_7576443
  simp only [CollatzResearch.WordTrace]
  refine ⟨276335578090848439292613983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184223718727232292861742655 276335578090848439292613983)
  ·
    refine ⟨414503367136272658938920975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276335578090848439292613983 414503367136272658938920975)
    ·
      refine ⟨621755050704408988408381463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414503367136272658938920975 621755050704408988408381463)
      ·
        refine ⟨932632576056613482612572195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621755050704408988408381463 932632576056613482612572195)
        ·
          refine ⟨1398948864084920223918858293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932632576056613482612572195 1398948864084920223918858293)
          ·
            refine ⟨131151456007961270992392965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1398948864084920223918858293 131151456007961270992392965)
            ·
              refine ⟨24590898001492738311073681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131151456007961270992392965 24590898001492738311073681)
              ·
                refine ⟨18443173501119553733305261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24590898001492738311073681 18443173501119553733305261)
                ·
                  refine ⟨6916190062919832649989473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18443173501119553733305261 6916190062919832649989473)
                  ·
                    refine ⟨5187142547189874487492105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6916190062919832649989473 5187142547189874487492105)
                    ·
                      refine ⟨3890356910392405865619079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5187142547189874487492105 3890356910392405865619079)
                      ·
                        rfl

theorem cell23_7576443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 2, 2].length) (baseStart_7576443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576443 prefixEnd_7576443 := by exact prefixLift 7576443
  have htrace : WordTrace (prefixWord ++ tailWord_7576443) baseStart_7576443 baseEnd_7576443 := by
    simpa [prefixWord, tailWord_7576443, baseEnd_7576443] using wordTrace_append hprefix tailTrace_7576443
  have hstable : (prefixWord ++ tailWord_7576443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576443).length < 2 ^ (prefixWord ++ tailWord_7576443).sum := by decide
  have hdescent : baseEnd_7576443 < baseStart_7576443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576487 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 2, 4]
def baseStart_7576487 : Nat := 118140960795 + 7576487 * 2 ^ 59
def prefixEnd_7576487 : Nat := 4983230072969 + 3 ^ 40 * 7576487 * 2
def baseEnd_7576487 : Nat := 1296793167847067897822959

theorem tailTrace_7576487 : CollatzResearch.WordTrace tailWord_7576487 prefixEnd_7576487 1296793167847067897822959 := by
  unfold tailWord_7576487
  simp only [CollatzResearch.WordTrace]
  refine ⟨276337182902689034807215715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184224788601792689871477143 276337182902689034807215715)
  ·
    refine ⟨414505774354033552210823573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276337182902689034807215715 414505774354033552210823573)
    ·
      refine ⟨19429958172845322759882355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 414505774354033552210823573 19429958172845322759882355)
      ·
        refine ⟨29144937259267984139823533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19429958172845322759882355 29144937259267984139823533)
        ·
          refine ⟨10929351472225494052433825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29144937259267984139823533 10929351472225494052433825)
          ·
            refine ⟨8197013604169120539325369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10929351472225494052433825 8197013604169120539325369)
            ·
              refine ⟨6147760203126840404494027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8197013604169120539325369 6147760203126840404494027)
              ·
                refine ⟨9221640304690260606741041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6147760203126840404494027 9221640304690260606741041)
                ·
                  refine ⟨6916230228517695455055781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9221640304690260606741041 6916230228517695455055781)
                  ·
                    refine ⟨1296793167847067897822959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916230228517695455055781 1296793167847067897822959)
                    ·
                      rfl

theorem cell23_7576487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_7576487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576487 prefixEnd_7576487 := by exact prefixLift 7576487
  have htrace : WordTrace (prefixWord ++ tailWord_7576487) baseStart_7576487 baseEnd_7576487 := by
    simpa [prefixWord, tailWord_7576487, baseEnd_7576487] using wordTrace_append hprefix tailTrace_7576487
  have hstable : (prefixWord ++ tailWord_7576487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576487).length < 2 ^ (prefixWord ++ tailWord_7576487).sum := by decide
  have hdescent : baseEnd_7576487 < baseStart_7576487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576497 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 1, 2, 3]
def baseStart_7576497 : Nat := 118140960795 + 7576497 * 2 ^ 59
def prefixEnd_7576497 : Nat := 4983230072969 + 3 ^ 40 * 7576497 * 2
def baseEnd_7576497 : Nat := 3890384638347748654343831

theorem tailTrace_7576497 : CollatzResearch.WordTrace tailWord_7576497 prefixEnd_7576497 3890384638347748654343831 := by
  unfold tailWord_7576497
  simp only [CollatzResearch.WordTrace]
  refine ⟨276337547632652806515079745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184225031755101871010053163 276337547632652806515079745)
  ·
    refine ⟨207253160724489604886309809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276337547632652806515079745 207253160724489604886309809)
    ·
      refine ⟨155439870543367203664732357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207253160724489604886309809 155439870543367203664732357)
      ·
        refine ⟨29144975726881350687137317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155439870543367203664732357 29144975726881350687137317)
        ·
          refine ⟨5464682948790253253838247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29144975726881350687137317 5464682948790253253838247)
          ·
            refine ⟨8197024423185379880757371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464682948790253253838247 8197024423185379880757371)
            ·
              refine ⟨12295536634778069821136057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197024423185379880757371 12295536634778069821136057)
              ·
                refine ⟨9221652476083552365852043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12295536634778069821136057 9221652476083552365852043)
                ·
                  refine ⟨13832478714125328548778065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9221652476083552365852043 13832478714125328548778065)
                  ·
                    refine ⟨10374359035593996411583549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13832478714125328548778065 10374359035593996411583549)
                    ·
                      refine ⟨3890384638347748654343831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10374359035593996411583549 3890384638347748654343831)
                      ·
                        rfl

theorem cell23_7576497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_7576497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576497 prefixEnd_7576497 := by exact prefixLift 7576497
  have htrace : WordTrace (prefixWord ++ tailWord_7576497) baseStart_7576497 baseEnd_7576497 := by
    simpa [prefixWord, tailWord_7576497, baseEnd_7576497] using wordTrace_append hprefix tailTrace_7576497
  have hstable : (prefixWord ++ tailWord_7576497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576497).length < 2 ^ (prefixWord ++ tailWord_7576497).sum := by decide
  have hdescent : baseEnd_7576497 < baseStart_7576497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576499 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 4]
def baseStart_7576499 : Nat := 118140960795 + 7576499 * 2 ^ 59
def prefixEnd_7576499 : Nat := 4983230072969 + 3 ^ 40 * 7576499 * 2
def baseEnd_7576499 : Nat := 3890385665309057646518821

theorem tailTrace_7576499 : CollatzResearch.WordTrace tailWord_7576499 prefixEnd_7576499 3890385665309057646518821 := by
  unfold tailWord_7576499
  simp only [CollatzResearch.WordTrace]
  refine ⟨276337620578645560856652551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184225080385763707237768367 276337620578645560856652551)
  ·
    refine ⟨414506430867968341284978827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276337620578645560856652551 414506430867968341284978827)
    ·
      refine ⟨621759646301952511927468241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414506430867968341284978827 621759646301952511927468241)
      ·
        refine ⟨466319734726464383945601181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 621759646301952511927468241 466319734726464383945601181)
        ·
          refine ⟨174869900522424143979600443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 466319734726464383945601181 174869900522424143979600443)
          ·
            refine ⟨262304850783636215969400665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174869900522424143979600443 262304850783636215969400665)
            ·
              refine ⟨196728638087727161977050499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262304850783636215969400665 196728638087727161977050499)
              ·
                refine ⟨295092957131590742965575749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196728638087727161977050499 295092957131590742965575749)
                ·
                  refine ⟨55329929462173264306045453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 295092957131590742965575749 55329929462173264306045453)
                  ·
                    refine ⟨20748723548314974114767045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55329929462173264306045453 20748723548314974114767045)
                    ·
                      refine ⟨3890385665309057646518821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20748723548314974114767045 3890385665309057646518821)
                      ·
                        rfl

theorem cell23_7576499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_7576499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576499 prefixEnd_7576499 := by exact prefixLift 7576499
  have htrace : WordTrace (prefixWord ++ tailWord_7576499) baseStart_7576499 baseEnd_7576499 := by
    simpa [prefixWord, tailWord_7576499, baseEnd_7576499] using wordTrace_append hprefix tailTrace_7576499
  have hstable : (prefixWord ++ tailWord_7576499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576499).length < 2 ^ (prefixWord ++ tailWord_7576499).sum := by decide
  have hdescent : baseEnd_7576499 < baseStart_7576499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576536 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_7576536 : Nat := 118140960795 + 7576536 * 2 ^ 59
def prefixEnd_7576536 : Nat := 4983230072969 + 3 ^ 40 * 7576536 * 2
def baseEnd_7576536 : Nat := 3890404664093274001756151

theorem tailTrace_7576536 : CollatzResearch.WordTrace tailWord_7576536 prefixEnd_7576536 3890404664093274001756151 := by
  unfold tailWord_7576536
  simp only [CollatzResearch.WordTrace]
  refine ⟨138169485039755758087874731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184225980053007677450499641 138169485039755758087874731)
  ·
    refine ⟨207254227559633637131812097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138169485039755758087874731 207254227559633637131812097)
    ·
      refine ⟨155440670669725227848859073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207254227559633637131812097 155440670669725227848859073)
      ·
        refine ⟨116580503002293920886644305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155440670669725227848859073 116580503002293920886644305)
        ·
          refine ⟨87435377251720440664983229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116580503002293920886644305 87435377251720440664983229)
          ·
            refine ⟨32788266469395165249368711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87435377251720440664983229 32788266469395165249368711)
            ·
              refine ⟨49182399704092747874053067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32788266469395165249368711 49182399704092747874053067)
              ·
                refine ⟨73773599556139121811079601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49182399704092747874053067 73773599556139121811079601)
                ·
                  refine ⟨55330199667104341358309701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73773599556139121811079601 55330199667104341358309701)
                  ·
                    refine ⟨10374412437582064004683069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55330199667104341358309701 10374412437582064004683069)
                    ·
                      refine ⟨3890404664093274001756151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10374412437582064004683069 3890404664093274001756151)
                      ·
                        rfl

theorem cell23_7576536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_7576536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576536 prefixEnd_7576536 := by exact prefixLift 7576536
  have htrace : WordTrace (prefixWord ++ tailWord_7576536) baseStart_7576536 baseEnd_7576536 := by
    simpa [prefixWord, tailWord_7576536, baseEnd_7576536] using wordTrace_append hprefix tailTrace_7576536
  have hstable : (prefixWord ++ tailWord_7576536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576536).length < 2 ^ (prefixWord ++ tailWord_7576536).sum := by decide
  have hdescent : baseEnd_7576536 < baseStart_7576536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576643 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 3]
def baseStart_7576643 : Nat := 118140960795 + 7576643 * 2 ^ 59
def prefixEnd_7576643 : Nat := 4983230072969 + 3 ^ 40 * 7576643 * 2
def baseEnd_7576643 : Nat := 3890459606523305083118159

theorem tailTrace_7576643 : CollatzResearch.WordTrace tailWord_7576643 prefixEnd_7576643 3890459606523305083118159 := by
  unfold tailWord_7576643
  simp only [CollatzResearch.WordTrace]
  refine ⟨276342872690123873449894583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184228581793415915633263055 276342872690123873449894583)
  ·
    refine ⟨414514309035185810174841875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276342872690123873449894583 414514309035185810174841875)
    ·
      refine ⟨621771463552778715262262813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414514309035185810174841875 621771463552778715262262813)
      ·
        refine ⟨233164298832292018223348555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 621771463552778715262262813 233164298832292018223348555)
        ·
          refine ⟨349746448248438027335022833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233164298832292018223348555 349746448248438027335022833)
          ·
            refine ⟨262309836186328520501267125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349746448248438027335022833 262309836186328520501267125)
            ·
              refine ⟨24591547142468298796993793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262309836186328520501267125 24591547142468298796993793)
              ·
                refine ⟨18443660356851224097745345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24591547142468298796993793 18443660356851224097745345)
                ·
                  refine ⟨13832745267638418073309009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18443660356851224097745345 13832745267638418073309009)
                  ·
                    refine ⟨10374558950728813554981757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13832745267638418073309009 10374558950728813554981757)
                    ·
                      refine ⟨3890459606523305083118159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10374558950728813554981757 3890459606523305083118159)
                      ·
                        rfl

theorem cell23_7576643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_7576643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576643 prefixEnd_7576643 := by exact prefixLift 7576643
  have htrace : WordTrace (prefixWord ++ tailWord_7576643) baseStart_7576643 baseEnd_7576643 := by
    simpa [prefixWord, tailWord_7576643, baseEnd_7576643] using wordTrace_append hprefix tailTrace_7576643
  have hstable : (prefixWord ++ tailWord_7576643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576643).length < 2 ^ (prefixWord ++ tailWord_7576643).sum := by decide
  have hdescent : baseEnd_7576643 < baseStart_7576643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576650 : List Nat := [3, 1, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_7576650 : Nat := 118140960795 + 7576650 * 2 ^ 59
def prefixEnd_7576650 : Nat := 4983230072969 + 3 ^ 40 * 7576650 * 2
def baseEnd_7576650 : Nat := 1296821066962628851910209

theorem tailTrace_7576650 : CollatzResearch.WordTrace tailWord_7576650 prefixEnd_7576650 1296821066962628851910209 := by
  unfold tailWord_7576650
  simp only [CollatzResearch.WordTrace]
  refine ⟨69085782000274628411349851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184228752000732342430266269 69085782000274628411349851)
  ·
    refine ⟨103628673000411942617024777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69085782000274628411349851 103628673000411942617024777)
    ·
      refine ⟨77721504750308956962768583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103628673000411942617024777 77721504750308956962768583)
      ·
        refine ⟨116582257125463435444152875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77721504750308956962768583 116582257125463435444152875)
        ·
          refine ⟨174873385688195153166229313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116582257125463435444152875 174873385688195153166229313)
          ·
            refine ⟨131155039266146364874671985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174873385688195153166229313 131155039266146364874671985)
            ·
              refine ⟨98366279449609773656003989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131155039266146364874671985 98366279449609773656003989)
              ·
                refine ⟨4610919349200458140125187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98366279449609773656003989 4610919349200458140125187)
                ·
                  refine ⟨6916379023800687210187781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610919349200458140125187 6916379023800687210187781)
                  ·
                    refine ⟨1296821066962628851910209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916379023800687210187781 1296821066962628851910209)
                    ·
                      rfl

theorem cell23_7576650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_7576650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576650 prefixEnd_7576650 := by exact prefixLift 7576650
  have htrace : WordTrace (prefixWord ++ tailWord_7576650) baseStart_7576650 baseEnd_7576650 := by
    simpa [prefixWord, tailWord_7576650, baseEnd_7576650] using wordTrace_append hprefix tailTrace_7576650
  have hstable : (prefixWord ++ tailWord_7576650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576650).length < 2 ^ (prefixWord ++ tailWord_7576650).sum := by decide
  have hdescent : baseEnd_7576650 < baseStart_7576650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576700 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_7576700 : Nat := 118140960795 + 7576700 * 2 ^ 59
def prefixEnd_7576700 : Nat := 4983230072969 + 3 ^ 40 * 7576700 * 2
def baseEnd_7576700 : Nat := 3890488874920611360105397

theorem tailTrace_7576700 : CollatzResearch.WordTrace tailWord_7576700 prefixEnd_7576700 3890488874920611360105397 := by
  unfold tailWord_7576700
  simp only [CollatzResearch.WordTrace]
  refine ⟨138172475825458686092359777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184229967767278248123146369 138172475825458686092359777)
  ·
    refine ⟨103629356869094014569269833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138172475825458686092359777 103629356869094014569269833)
    ·
      refine ⟨77722017651820510926952375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103629356869094014569269833 77722017651820510926952375)
      ·
        refine ⟨116583026477730766390428563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77722017651820510926952375 116583026477730766390428563)
        ·
          refine ⟨174874539716596149585642845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116583026477730766390428563 174874539716596149585642845)
          ·
            refine ⟨65577952393723556094616067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174874539716596149585642845 65577952393723556094616067)
            ·
              refine ⟨98366928590585334141924101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65577952393723556094616067 98366928590585334141924101)
              ·
                refine ⟨18443799110734750151610769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98366928590585334141924101 18443799110734750151610769)
                ·
                  refine ⟨13832849333051062613708077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18443799110734750151610769 13832849333051062613708077)
                  ·
                    refine ⟨5187318499894148480140529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13832849333051062613708077 5187318499894148480140529)
                    ·
                      refine ⟨3890488874920611360105397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5187318499894148480140529 3890488874920611360105397)
                      ·
                        rfl

theorem cell23_7576700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_7576700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576700 prefixEnd_7576700 := by exact prefixLift 7576700
  have htrace : WordTrace (prefixWord ++ tailWord_7576700) baseStart_7576700 baseEnd_7576700 := by
    simpa [prefixWord, tailWord_7576700, baseEnd_7576700] using wordTrace_append hprefix tailTrace_7576700
  have hstable : (prefixWord ++ tailWord_7576700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576700).length < 2 ^ (prefixWord ++ tailWord_7576700).sum := by decide
  have hdescent : baseEnd_7576700 < baseStart_7576700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576707 : List Nat := [1, 1, 1, 3, 3, 2, 3, 4, 1, 1, 3]
def baseStart_7576707 : Nat := 118140960795 + 7576707 * 2 ^ 59
def prefixEnd_7576707 : Nat := 4983230072969 + 3 ^ 40 * 7576707 * 2
def baseEnd_7576707 : Nat := 3890492469285192832717865

theorem tailTrace_7576707 : CollatzResearch.WordTrace tailWord_7576707 prefixEnd_7576707 3890492469285192832717865 := by
  unfold tailWord_7576707
  simp only [CollatzResearch.WordTrace]
  refine ⟨276345206961892012380224375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184230137974594674920149583 276345206961892012380224375)
  ·
    refine ⟨414517810442838018570336563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276345206961892012380224375 414517810442838018570336563)
    ·
      refine ⟨621776715664257027855504845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414517810442838018570336563 621776715664257027855504845)
      ·
        refine ⟨233166268374096385445814317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 621776715664257027855504845 233166268374096385445814317)
        ·
          refine ⟨87437350640286144542180369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233166268374096385445814317 87437350640286144542180369)
          ·
            refine ⟨65578012980214608406635277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87437350640286144542180369 65578012980214608406635277)
            ·
              refine ⟨24591754867580478152488229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65578012980214608406635277 24591754867580478152488229)
              ·
                refine ⟨4610954037671339653591543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24591754867580478152488229 4610954037671339653591543)
                ·
                  refine ⟨6916431056507009480387315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610954037671339653591543 6916431056507009480387315)
                  ·
                    refine ⟨10374646584760514220580973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6916431056507009480387315 10374646584760514220580973)
                    ·
                      refine ⟨3890492469285192832717865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10374646584760514220580973 3890492469285192832717865)
                      ·
                        rfl

theorem cell23_7576707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_7576707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576707 prefixEnd_7576707 := by exact prefixLift 7576707
  have htrace : WordTrace (prefixWord ++ tailWord_7576707) baseStart_7576707 baseEnd_7576707 := by
    simpa [prefixWord, tailWord_7576707, baseEnd_7576707] using wordTrace_append hprefix tailTrace_7576707
  have hstable : (prefixWord ++ tailWord_7576707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576707).length < 2 ^ (prefixWord ++ tailWord_7576707).sum := by decide
  have hdescent : baseEnd_7576707 < baseStart_7576707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576713 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_7576713 : Nat := 118140960795 + 7576713 * 2 ^ 59
def prefixEnd_7576713 : Nat := 4983230072969 + 3 ^ 40 * 7576713 * 2
def baseEnd_7576713 : Nat := 3890495550169119809242837

theorem tailTrace_7576713 : CollatzResearch.WordTrace tailWord_7576713 prefixEnd_7576713 3890495550169119809242837 := by
  unfold tailWord_7576713
  simp only [CollatzResearch.WordTrace]
  refine ⟨276345425799870275404942793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184230283866580183603295195 276345425799870275404942793)
  ·
    refine ⟨207259069349902706553707095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276345425799870275404942793 207259069349902706553707095)
    ·
      refine ⟨310888604024854059830560643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207259069349902706553707095 310888604024854059830560643)
      ·
        refine ⟨466332906037281089745840965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310888604024854059830560643 466332906037281089745840965)
        ·
          refine ⟨87437419881990204327345181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466332906037281089745840965 87437419881990204327345181)
          ·
            refine ⟨32789032455746326622754443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87437419881990204327345181 32789032455746326622754443)
            ·
              refine ⟨49183548683619489934131665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32789032455746326622754443 49183548683619489934131665)
              ·
                refine ⟨36887661512714617450598749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49183548683619489934131665 36887661512714617450598749)
                ·
                  refine ⟨13832873067267981543974531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36887661512714617450598749 13832873067267981543974531)
                  ·
                    refine ⟨20749309600901972315961797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13832873067267981543974531 20749309600901972315961797)
                    ·
                      refine ⟨3890495550169119809242837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20749309600901972315961797 3890495550169119809242837)
                      ·
                        rfl

theorem cell23_7576713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_7576713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576713 prefixEnd_7576713 := by exact prefixLift 7576713
  have htrace : WordTrace (prefixWord ++ tailWord_7576713) baseStart_7576713 baseEnd_7576713 := by
    simpa [prefixWord, tailWord_7576713, baseEnd_7576713] using wordTrace_append hprefix tailTrace_7576713
  have hstable : (prefixWord ++ tailWord_7576713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576713).length < 2 ^ (prefixWord ++ tailWord_7576713).sum := by decide
  have hdescent : baseEnd_7576713 < baseStart_7576713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576730 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7576730 : Nat := 118140960795 + 7576730 * 2 ^ 59
def prefixEnd_7576730 : Nat := 4983230072969 + 3 ^ 40 * 7576730 * 2
def baseEnd_7576730 : Nat := 3890504279340246242730259

theorem tailTrace_7576730 : CollatzResearch.WordTrace tailWord_7576730 prefixEnd_7576730 3890504279340246242730259 := by
  unfold tailWord_7576730
  simp only [CollatzResearch.WordTrace]
  refine ⟨69086511460202171827077911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184230697227205791538874429 69086511460202171827077911)
  ·
    refine ⟨103629767190303257740616867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69086511460202171827077911 103629767190303257740616867)
    ·
      refine ⟨155444650785454886610925301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103629767190303257740616867 155444650785454886610925301)
      ·
        refine ⟨14572936011136395619774247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155444650785454886610925301 14572936011136395619774247)
        ·
          refine ⟨21859404016704593429661371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14572936011136395619774247 21859404016704593429661371)
          ·
            refine ⟨32789106025056890144492057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21859404016704593429661371 32789106025056890144492057)
            ·
              refine ⟨24591829518792667608369043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32789106025056890144492057 24591829518792667608369043)
              ·
                refine ⟨36887744278189001412553565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24591829518792667608369043 36887744278189001412553565)
                ·
                  refine ⟨13832904104320875529707587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36887744278189001412553565 13832904104320875529707587)
                  ·
                    refine ⟨20749356156481313294561381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13832904104320875529707587 20749356156481313294561381)
                    ·
                      refine ⟨3890504279340246242730259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20749356156481313294561381 3890504279340246242730259)
                      ·
                        rfl

theorem cell23_7576730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7576730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576730 prefixEnd_7576730 := by exact prefixLift 7576730
  have htrace : WordTrace (prefixWord ++ tailWord_7576730) baseStart_7576730 baseEnd_7576730 := by
    simpa [prefixWord, tailWord_7576730, baseEnd_7576730] using wordTrace_append hprefix tailTrace_7576730
  have hstable : (prefixWord ++ tailWord_7576730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576730).length < 2 ^ (prefixWord ++ tailWord_7576730).sum := by decide
  have hdescent : baseEnd_7576730 < baseStart_7576730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576734 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_7576734 : Nat := 118140960795 + 7576734 * 2 ^ 59
def prefixEnd_7576734 : Nat := 4983230072969 + 3 ^ 40 * 7576734 * 2
def baseEnd_7576734 : Nat := 3890506333262864227080241

theorem tailTrace_7576734 : CollatzResearch.WordTrace tailWord_7576734 prefixEnd_7576734 3890506333262864227080241 := by
  unfold tailWord_7576734
  simp only [CollatzResearch.WordTrace]
  refine ⟨34543273966599274498932157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184230794488529463994304837 34543273966599274498932157)
  ·
    refine ⟨12953727737474727937099559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34543273966599274498932157 12953727737474727937099559)
    ·
      refine ⟨19430591606212091905649339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953727737474727937099559 19430591606212091905649339)
      ·
        refine ⟨29145887409318137858474009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19430591606212091905649339 29145887409318137858474009)
        ·
          refine ⟨21859415556988603393855507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29145887409318137858474009 21859415556988603393855507)
          ·
            refine ⟨32789123335482905090783261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21859415556988603393855507 32789123335482905090783261)
            ·
              refine ⟨12295921250806089409043723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32789123335482905090783261 12295921250806089409043723)
              ·
                refine ⟨18443881876209134113565585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12295921250806089409043723 18443881876209134113565585)
                ·
                  refine ⟨13832911407156850585174189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18443881876209134113565585 13832911407156850585174189)
                  ·
                    refine ⟨5187341777683818969440321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13832911407156850585174189 5187341777683818969440321)
                    ·
                      refine ⟨3890506333262864227080241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5187341777683818969440321 3890506333262864227080241)
                      ·
                        rfl

theorem cell23_7576734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_7576734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576734 prefixEnd_7576734 := by exact prefixLift 7576734
  have htrace : WordTrace (prefixWord ++ tailWord_7576734) baseStart_7576734 baseEnd_7576734 := by
    simpa [prefixWord, tailWord_7576734, baseEnd_7576734] using wordTrace_append hprefix tailTrace_7576734
  have hstable : (prefixWord ++ tailWord_7576734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576734).length < 2 ^ (prefixWord ++ tailWord_7576734).sum := by decide
  have hdescent : baseEnd_7576734 < baseStart_7576734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576753 : List Nat := [1, 2, 2, 5, 1, 2, 10]
def baseStart_7576753 : Nat := 118140960795 + 7576753 * 2 ^ 59
def prefixEnd_7576753 : Nat := 4983230072969 + 3 ^ 40 * 7576753 * 2
def baseEnd_7576753 : Nat := 48031062832040736453613

theorem tailTrace_7576753 : CollatzResearch.WordTrace tailWord_7576753 prefixEnd_7576753 48031062832040736453613 := by
  unfold tailWord_7576753
  simp only [CollatzResearch.WordTrace]
  refine ⟨276346884719725362236398913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184231256479816908157599275 276346884719725362236398913)
  ·
    refine ⟨207260163539794021677299185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276346884719725362236398913 207260163539794021677299185)
    ·
      refine ⟨155445122654845516257974389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207260163539794021677299185 155445122654845516257974389)
      ·
        refine ⟨14572980248891767149185099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155445122654845516257974389 14572980248891767149185099)
        ·
          refine ⟨21859470373337650723777649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14572980248891767149185099 21859470373337650723777649)
          ·
            refine ⟨16394602780003238042833237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21859470373337650723777649 16394602780003238042833237)
            ·
              refine ⟨48031062832040736453613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16394602780003238042833237 48031062832040736453613)
              ·
                rfl

theorem cell23_7576753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 10].length) (baseStart_7576753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576753 prefixEnd_7576753 := by exact prefixLift 7576753
  have htrace : WordTrace (prefixWord ++ tailWord_7576753) baseStart_7576753 baseEnd_7576753 := by
    simpa [prefixWord, tailWord_7576753, baseEnd_7576753] using wordTrace_append hprefix tailTrace_7576753
  have hstable : (prefixWord ++ tailWord_7576753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576753).length < 2 ^ (prefixWord ++ tailWord_7576753).sum := by decide
  have hdescent : baseEnd_7576753 < baseStart_7576753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576764 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_7576764 : Nat := 118140960795 + 7576764 * 2 ^ 59
def prefixEnd_7576764 : Nat := 4983230072969 + 3 ^ 40 * 7576764 * 2
def baseEnd_7576764 : Nat := 3890521737682499109705103

theorem tailTrace_7576764 : CollatzResearch.WordTrace tailWord_7576764 prefixEnd_7576764 3890521737682499109705103 := by
  unfold tailWord_7576764
  simp only [CollatzResearch.WordTrace]
  refine ⟨138173642961342755557524673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184231523948457007410032897 138173642961342755557524673)
  ·
    refine ⟨103630232221007066668143505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138173642961342755557524673 103630232221007066668143505)
    ·
      refine ⟨77722674165755300001107629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103630232221007066668143505 77722674165755300001107629)
      ·
        refine ⟨29146002812158237500415361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77722674165755300001107629 29146002812158237500415361)
        ·
          refine ⟨21859502109118678125311521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29146002812158237500415361 21859502109118678125311521)
          ·
            refine ⟨16394626581839008593983641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21859502109118678125311521 16394626581839008593983641)
            ·
              refine ⟨12295969936379256445487731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16394626581839008593983641 12295969936379256445487731)
              ·
                refine ⟨18443954904568884668231597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12295969936379256445487731 18443954904568884668231597)
                ·
                  refine ⟨6916483089213331750586849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18443954904568884668231597 6916483089213331750586849)
                  ·
                    refine ⟨5187362316909998812940137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6916483089213331750586849 5187362316909998812940137)
                    ·
                      refine ⟨3890521737682499109705103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5187362316909998812940137 3890521737682499109705103)
                      ·
                        rfl

theorem cell23_7576764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_7576764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576764 prefixEnd_7576764 := by exact prefixLift 7576764
  have htrace : WordTrace (prefixWord ++ tailWord_7576764) baseStart_7576764 baseEnd_7576764 := by
    simpa [prefixWord, tailWord_7576764, baseEnd_7576764] using wordTrace_append hprefix tailTrace_7576764
  have hstable : (prefixWord ++ tailWord_7576764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576764).length < 2 ^ (prefixWord ++ tailWord_7576764).sum := by decide
  have hdescent : baseEnd_7576764 < baseStart_7576764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576781 : List Nat := [1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7576781 : Nat := 118140960795 + 7576781 * 2 ^ 59
def prefixEnd_7576781 : Nat := 4983230072969 + 3 ^ 40 * 7576781 * 2
def baseEnd_7576781 : Nat := 3890530466853625543192525

theorem tailTrace_7576781 : CollatzResearch.WordTrace tailWord_7576781 prefixEnd_7576781 3890530466853625543192525 := by
  unfold tailWord_7576781
  simp only [CollatzResearch.WordTrace]
  refine ⟨276347905963623923018418197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184231937309082615345612131 276347905963623923018418197)
  ·
    refine ⟨12953808092044871391488353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 276347905963623923018418197 12953808092044871391488353)
    ·
      refine ⟨9715356069033653543616265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12953808092044871391488353 9715356069033653543616265)
      ·
        refine ⟨7286517051775240157712199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9715356069033653543616265 7286517051775240157712199)
        ·
          refine ⟨10929775577662860236568299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7286517051775240157712199 10929775577662860236568299)
          ·
            refine ⟨16394663366494290354852449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929775577662860236568299 16394663366494290354852449)
            ·
              refine ⟨12295997524870717766139337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16394663366494290354852449 12295997524870717766139337)
              ·
                refine ⟨9221998143653038324604503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12295997524870717766139337 9221998143653038324604503)
                ·
                  refine ⟨13832997215479557486906755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9221998143653038324604503 13832997215479557486906755)
                  ·
                    refine ⟨20749495823219336230360133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13832997215479557486906755 20749495823219336230360133)
                    ·
                      refine ⟨3890530466853625543192525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20749495823219336230360133 3890530466853625543192525)
                      ·
                        rfl

theorem cell23_7576781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7576781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576781 prefixEnd_7576781 := by exact prefixLift 7576781
  have htrace : WordTrace (prefixWord ++ tailWord_7576781) baseStart_7576781 baseEnd_7576781 := by
    simpa [prefixWord, tailWord_7576781, baseEnd_7576781] using wordTrace_append hprefix tailTrace_7576781
  have hstable : (prefixWord ++ tailWord_7576781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576781).length < 2 ^ (prefixWord ++ tailWord_7576781).sum := by decide
  have hdescent : baseEnd_7576781 < baseStart_7576781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576823 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_7576823 : Nat := 118140960795 + 7576823 * 2 ^ 59
def prefixEnd_7576823 : Nat := 4983230072969 + 3 ^ 40 * 7576823 * 2
def baseEnd_7576823 : Nat := 3890552033041114378867331

theorem tailTrace_7576823 : CollatzResearch.WordTrace tailWord_7576823 prefixEnd_7576823 3890552033041114378867331 := by
  unfold tailWord_7576823
  simp only [CollatzResearch.WordTrace]
  refine ⟨276349437829471764191447123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184232958552981176127631415 276349437829471764191447123)
  ·
    refine ⟨414524156744207646287170685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276349437829471764191447123 414524156744207646287170685)
    ·
      refine ⟨155446558779077867357689007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414524156744207646287170685 155446558779077867357689007)
      ·
        refine ⟨233169838168616801036533511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155446558779077867357689007 233169838168616801036533511)
        ·
          refine ⟨349754757252925201554800267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233169838168616801036533511 349754757252925201554800267)
          ·
            refine ⟨524632135879387802332200401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349754757252925201554800267 524632135879387802332200401)
            ·
              refine ⟨393474101909540851749150301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524632135879387802332200401 393474101909540851749150301)
              ·
                refine ⟨147552788216077819405931363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393474101909540851749150301 147552788216077819405931363)
                ·
                  refine ⟨221329182324116729108897045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147552788216077819405931363 221329182324116729108897045)
                  ·
                    refine ⟨10374805421442971676979549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 221329182324116729108897045 10374805421442971676979549)
                    ·
                      refine ⟨3890552033041114378867331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10374805421442971676979549 3890552033041114378867331)
                      ·
                        rfl

theorem cell23_7576823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_7576823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576823 prefixEnd_7576823 := by exact prefixLift 7576823
  have htrace : WordTrace (prefixWord ++ tailWord_7576823) baseStart_7576823 baseEnd_7576823 := by
    simpa [prefixWord, tailWord_7576823, baseEnd_7576823] using wordTrace_append hprefix tailTrace_7576823
  have hstable : (prefixWord ++ tailWord_7576823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576823).length < 2 ^ (prefixWord ++ tailWord_7576823).sum := by decide
  have hdescent : baseEnd_7576823 < baseStart_7576823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576873 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 8, 5]
def baseStart_7576873 : Nat := 118140960795 + 7576873 * 2 ^ 59
def prefixEnd_7576873 : Nat := 4983230072969 + 3 ^ 40 * 7576873 * 2
def baseEnd_7576873 : Nat := 1296859235691279727747367

theorem tailTrace_7576873 : CollatzResearch.WordTrace tailWord_7576873 prefixEnd_7576873 1296859235691279727747367 := by
  unfold tailWord_7576873
  simp only [CollatzResearch.WordTrace]
  refine ⟨276351261479290622730767273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184234174319527081820511515 276351261479290622730767273)
  ·
    refine ⟨207263446109467967048075455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276351261479290622730767273 207263446109467967048075455)
    ·
      refine ⟨310895169164201950572113183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207263446109467967048075455 310895169164201950572113183)
      ·
        refine ⟨466342753746302925858169775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310895169164201950572113183 466342753746302925858169775)
        ·
          refine ⟨699514130619454388787254663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466342753746302925858169775 699514130619454388787254663)
          ·
            refine ⟨1049271195929181583180881995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699514130619454388787254663 1049271195929181583180881995)
            ·
              refine ⟨1573906793893772374771322993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1049271195929181583180881995 1573906793893772374771322993)
              ·
                refine ⟨1180430095420329281078492245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1573906793893772374771322993 1180430095420329281078492245)
                ·
                  refine ⟨13833165180706983762638581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1180430095420329281078492245 13833165180706983762638581)
                  ·
                    refine ⟨1296859235691279727747367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13833165180706983762638581 1296859235691279727747367)
                    ·
                      rfl

theorem cell23_7576873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_7576873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576873 prefixEnd_7576873 := by exact prefixLift 7576873
  have htrace : WordTrace (prefixWord ++ tailWord_7576873) baseStart_7576873 baseEnd_7576873 := by
    simpa [prefixWord, tailWord_7576873, baseEnd_7576873] using wordTrace_append hprefix tailTrace_7576873
  have hstable : (prefixWord ++ tailWord_7576873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576873).length < 2 ^ (prefixWord ++ tailWord_7576873).sum := by decide
  have hdescent : baseEnd_7576873 < baseStart_7576873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576880 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 1, 7, 2]
def baseStart_7576880 : Nat := 118140960795 + 7576880 * 2 ^ 59
def prefixEnd_7576880 : Nat := 4983230072969 + 3 ^ 40 * 7576880 * 2
def baseEnd_7576880 : Nat := 3890581301438420655854569

theorem tailTrace_7576880 : CollatzResearch.WordTrace tailWord_7576880 prefixEnd_7576880 3890581301438420655854569 := by
  unfold tailWord_7576880
  simp only [CollatzResearch.WordTrace]
  refine ⟨138175758395132631463136047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184234344526843508617514729 138175758395132631463136047)
  ·
    refine ⟨207263637592698947194704071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138175758395132631463136047 207263637592698947194704071)
    ·
      refine ⟨310895456389048420792056107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207263637592698947194704071 310895456389048420792056107)
      ·
        refine ⟨466343184583572631188084161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310895456389048420792056107 466343184583572631188084161)
        ·
          refine ⟨349757388437679473391063121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466343184583572631188084161 349757388437679473391063121)
          ·
            refine ⟨262318041328259605043297341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349757388437679473391063121 262318041328259605043297341)
            ·
              refine ⟨98369265498097351891236503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262318041328259605043297341 98369265498097351891236503)
              ·
                refine ⟨147553898247146027836854755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98369265498097351891236503 147553898247146027836854755)
                ·
                  refine ⟨221330847370719041755282133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147553898247146027836854755 221330847370719041755282133)
                  ·
                    refine ⟨5187441735251227541139425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 221330847370719041755282133 5187441735251227541139425)
                    ·
                      refine ⟨3890581301438420655854569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5187441735251227541139425 3890581301438420655854569)
                      ·
                        rfl

theorem cell23_7576880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 7, 2].length) (baseStart_7576880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576880 prefixEnd_7576880 := by exact prefixLift 7576880
  have htrace : WordTrace (prefixWord ++ tailWord_7576880) baseStart_7576880 baseEnd_7576880 := by
    simpa [prefixWord, tailWord_7576880, baseEnd_7576880] using wordTrace_append hprefix tailTrace_7576880
  have hstable : (prefixWord ++ tailWord_7576880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576880).length < 2 ^ (prefixWord ++ tailWord_7576880).sum := by decide
  have hdescent : baseEnd_7576880 < baseStart_7576880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576910 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_7576910 : Nat := 118140960795 + 7576910 * 2 ^ 59
def prefixEnd_7576910 : Nat := 4983230072969 + 3 ^ 40 * 7576910 * 2
def baseEnd_7576910 : Nat := 3890596705858055538479431

theorem tailTrace_7576910 : CollatzResearch.WordTrace tailWord_7576910 prefixEnd_7576910 3890596705858055538479431 := by
  unfold tailWord_7576910
  simp only [CollatzResearch.WordTrace]
  refine ⟨34544076372519572256233023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184235073986771052033242789 34544076372519572256233023)
  ·
    refine ⟨51816114558779358384349535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34544076372519572256233023 51816114558779358384349535)
    ·
      refine ⟨77724171838169037576524303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51816114558779358384349535 77724171838169037576524303)
      ·
        refine ⟨116586257757253556364786455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77724171838169037576524303 116586257757253556364786455)
        ·
          refine ⟨174879386635880334547179683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116586257757253556364786455 174879386635880334547179683)
          ·
            refine ⟨262319079953820501820769525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174879386635880334547179683 262319079953820501820769525)
            ·
              refine ⟨24592413745670672045697143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262319079953820501820769525 24592413745670672045697143)
              ·
                refine ⟨36888620618506008068545715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24592413745670672045697143 36888620618506008068545715)
                ·
                  refine ⟨55332930927759012102818573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36888620618506008068545715 55332930927759012102818573)
                  ·
                    refine ⟨20749849097909629538556965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55332930927759012102818573 20749849097909629538556965)
                    ·
                      refine ⟨3890596705858055538479431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20749849097909629538556965 3890596705858055538479431)
                      ·
                        rfl

theorem cell23_7576910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_7576910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576910 prefixEnd_7576910 := by exact prefixLift 7576910
  have htrace : WordTrace (prefixWord ++ tailWord_7576910) baseStart_7576910 baseEnd_7576910 := by
    simpa [prefixWord, tailWord_7576910, baseEnd_7576910] using wordTrace_append hprefix tailTrace_7576910
  have hstable : (prefixWord ++ tailWord_7576910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576910).length < 2 ^ (prefixWord ++ tailWord_7576910).sum := by decide
  have hdescent : baseEnd_7576910 < baseStart_7576910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576920 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 5, 4]
def baseStart_7576920 : Nat := 118140960795 + 7576920 * 2 ^ 59
def prefixEnd_7576920 : Nat := 4983230072969 + 3 ^ 40 * 7576920 * 2
def baseEnd_7576920 : Nat := 1296867280221533499784795

theorem tailTrace_7576920 : CollatzResearch.WordTrace tailWord_7576920 prefixEnd_7576920 1296867280221533499784795 := by
  unfold tailWord_7576920
  simp only [CollatzResearch.WordTrace]
  refine ⟨138176487855060174878864107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184235317140080233171818809 138176487855060174878864107)
  ·
    refine ⟨207264731782590262318296161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138176487855060174878864107 207264731782590262318296161)
    ·
      refine ⟨155448548836942696738722121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207264731782590262318296161 155448548836942696738722121)
      ·
        refine ⟨116586411627707022554041591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155448548836942696738722121 116586411627707022554041591)
        ·
          refine ⟨174879617441560533831062387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116586411627707022554041591 174879617441560533831062387)
          ·
            refine ⟨262319426162340800746593581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174879617441560533831062387 262319426162340800746593581)
            ·
              refine ⟨98369784810877800279972593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262319426162340800746593581 98369784810877800279972593)
              ·
                refine ⟨73777338608158350209979445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98369784810877800279972593 73777338608158350209979445)
                ·
                  refine ⟨6916625494514845332185573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73777338608158350209979445 6916625494514845332185573)
                  ·
                    refine ⟨1296867280221533499784795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916625494514845332185573 1296867280221533499784795)
                    ·
                      rfl

theorem cell23_7576920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_7576920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576920 prefixEnd_7576920 := by exact prefixLift 7576920
  have htrace : WordTrace (prefixWord ++ tailWord_7576920) baseStart_7576920 baseEnd_7576920 := by
    simpa [prefixWord, tailWord_7576920, baseEnd_7576920] using wordTrace_append hprefix tailTrace_7576920
  have hstable : (prefixWord ++ tailWord_7576920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576920).length < 2 ^ (prefixWord ++ tailWord_7576920).sum := by decide
  have hdescent : baseEnd_7576920 < baseStart_7576920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7576988 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_7576988 : Nat := 118140960795 + 7576988 * 2 ^ 59
def prefixEnd_7576988 : Nat := 4983230072969 + 3 ^ 40 * 7576988 * 2
def baseEnd_7576988 : Nat := 1296878919116368744434691

theorem tailTrace_7576988 : CollatzResearch.WordTrace tailWord_7576988 prefixEnd_7576988 1296878919116368744434691 := by
  unfold tailWord_7576988
  simp only [CollatzResearch.WordTrace]
  refine ⟨138177727936936998685601809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184236970582582664914135745 138177727936936998685601809)
  ·
    refine ⟨103633295952702749014201357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138177727936936998685601809 103633295952702749014201357)
    ·
      refine ⟨38862485982263530880325509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103633295952702749014201357 38862485982263530880325509)
      ·
        refine ⟨7286716121674412040061033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38862485982263530880325509 7286716121674412040061033)
        ·
          refine ⟨5465037091255809030045775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7286716121674412040061033 5465037091255809030045775)
          ·
            refine ⟨8197555636883713545068663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465037091255809030045775 8197555636883713545068663)
            ·
              refine ⟨12296333455325570317602995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197555636883713545068663 12296333455325570317602995)
              ·
                refine ⟨18444500182988355476404493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12296333455325570317602995 18444500182988355476404493)
                ·
                  refine ⟨6916687568620633303651685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18444500182988355476404493 6916687568620633303651685)
                  ·
                    refine ⟨1296878919116368744434691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916687568620633303651685 1296878919116368744434691)
                    ·
                      rfl

theorem cell23_7576988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_7576988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7576988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7576988 prefixEnd_7576988 := by exact prefixLift 7576988
  have htrace : WordTrace (prefixWord ++ tailWord_7576988) baseStart_7576988 baseEnd_7576988 := by
    simpa [prefixWord, tailWord_7576988, baseEnd_7576988] using wordTrace_append hprefix tailTrace_7576988
  have hstable : (prefixWord ++ tailWord_7576988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7576988).length < 2 ^ (prefixWord ++ tailWord_7576988).sum := by decide
  have hdescent : baseEnd_7576988 < baseStart_7576988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7576988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577057 : List Nat := [1, 2, 3, 1, 2, 5, 1, 8]
def baseStart_7577057 : Nat := 118140960795 + 7577057 * 2 ^ 59
def prefixEnd_7577057 : Nat := 4983230072969 + 3 ^ 40 * 7577057 * 2
def baseEnd_7577057 : Nat := 144098969907935794938565

theorem tailTrace_7577057 : CollatzResearch.WordTrace tailWord_7577057 prefixEnd_7577057 144098969907935794938565 := by
  unfold tailWord_7577057
  simp only [CollatzResearch.WordTrace]
  refine ⟨276357972510624022155465425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184238648340416014770310283 276357972510624022155465425)
  ·
    refine ⟨207268479382968016616599069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276357972510624022155465425 207268479382968016616599069)
    ·
      refine ⟨77725679768613006231224651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207268479382968016616599069 77725679768613006231224651)
      ·
        refine ⟨116588519652919509346836977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77725679768613006231224651 116588519652919509346836977)
        ·
          refine ⟨87441389739689632010127733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116588519652919509346836977 87441389739689632010127733)
          ·
            refine ⟨8197630288095903000949475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87441389739689632010127733 8197630288095903000949475)
            ·
              refine ⟨12296445432143854501424213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197630288095903000949475 12296445432143854501424213)
              ·
                refine ⟨144098969907935794938565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12296445432143854501424213 144098969907935794938565)
                ·
                  rfl

theorem cell23_7577057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 8].length) (baseStart_7577057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577057 prefixEnd_7577057 := by exact prefixLift 7577057
  have htrace : WordTrace (prefixWord ++ tailWord_7577057) baseStart_7577057 baseEnd_7577057 := by
    simpa [prefixWord, tailWord_7577057, baseEnd_7577057] using wordTrace_append hprefix tailTrace_7577057
  have hstable : (prefixWord ++ tailWord_7577057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577057).length < 2 ^ (prefixWord ++ tailWord_7577057).sum := by decide
  have hdescent : baseEnd_7577057 < baseStart_7577057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577060 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_7577060 : Nat := 118140960795 + 7577060 * 2 ^ 59
def prefixEnd_7577060 : Nat := 4983230072969 + 3 ^ 40 * 7577060 * 2
def baseEnd_7577060 : Nat := 3890673727956229951603741

theorem tailTrace_7577060 : CollatzResearch.WordTrace tailWord_7577060 prefixEnd_7577060 3890673727956229951603741 := by
  unfold tailWord_7577060
  simp only [CollatzResearch.WordTrace]
  refine ⟨138179040964806576833912317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184238721286408769111883089 138179040964806576833912317)
  ·
    refine ⟨51817140361802466312717119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138179040964806576833912317 51817140361802466312717119)
    ·
      refine ⟨77725710542703699469075679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51817140361802466312717119 77725710542703699469075679)
      ·
        refine ⟨116588565814055549203613519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77725710542703699469075679 116588565814055549203613519)
        ·
          refine ⟨174882848721083323805420279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116588565814055549203613519 174882848721083323805420279)
          ·
            refine ⟨262324273081624985708130419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174882848721083323805420279 262324273081624985708130419)
            ·
              refine ⟨393486409622437478562195629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262324273081624985708130419 393486409622437478562195629)
              ·
                refine ⟨147557403608414054460823361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 393486409622437478562195629 147557403608414054460823361)
                ·
                  refine ⟨110668052706310540845617521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147557403608414054460823361 110668052706310540845617521)
                  ·
                    refine ⟨83001039529732905634213141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110668052706310540845617521 83001039529732905634213141)
                    ·
                      refine ⟨3890673727956229951603741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83001039529732905634213141 3890673727956229951603741)
                      ·
                        rfl

theorem cell23_7577060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_7577060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577060 prefixEnd_7577060 := by exact prefixLift 7577060
  have htrace : WordTrace (prefixWord ++ tailWord_7577060) baseStart_7577060 baseEnd_7577060 := by
    simpa [prefixWord, tailWord_7577060, baseEnd_7577060] using wordTrace_append hprefix tailTrace_7577060
  have hstable : (prefixWord ++ tailWord_7577060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577060).length < 2 ^ (prefixWord ++ tailWord_7577060).sum := by decide
  have hdescent : baseEnd_7577060 < baseStart_7577060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577074 : List Nat := [3, 2, 1, 4, 1, 2, 3, 7]
def baseStart_7577074 : Nat := 118140960795 + 7577074 * 2 ^ 59
def prefixEnd_7577074 : Nat := 4983230072969 + 3 ^ 40 * 7577074 * 2
def baseEnd_7577074 : Nat := 144099293210570107289951

theorem tailTrace_7577074 : CollatzResearch.WordTrace tailWord_7577074 prefixEnd_7577074 144099293210570107289951 := by
  unfold tailWord_7577074
  simp only [CollatzResearch.WordTrace]
  refine ⟨69089648137890608514708569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184239061701041622705889517 69089648137890608514708569)
  ·
    refine ⟨51817236103417956386031427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69089648137890608514708569 51817236103417956386031427)
    ·
      refine ⟨77725854155126934579047141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51817236103417956386031427 77725854155126934579047141)
      ·
        refine ⟨14573597654086300233571339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77725854155126934579047141 14573597654086300233571339)
        ·
          refine ⟨21860396481129450350357009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14573597654086300233571339 21860396481129450350357009)
          ·
            refine ⟨16395297360847087762767757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21860396481129450350357009 16395297360847087762767757)
            ·
              refine ⟨6148236510317657911037909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16395297360847087762767757 6148236510317657911037909)
              ·
                refine ⟨144099293210570107289951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6148236510317657911037909 144099293210570107289951)
                ·
                  rfl

theorem cell23_7577074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 7].length) (baseStart_7577074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577074 prefixEnd_7577074 := by exact prefixLift 7577074
  have htrace : WordTrace (prefixWord ++ tailWord_7577074) baseStart_7577074 baseEnd_7577074 := by
    simpa [prefixWord, tailWord_7577074, baseEnd_7577074] using wordTrace_append hprefix tailTrace_7577074
  have hstable : (prefixWord ++ tailWord_7577074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577074).length < 2 ^ (prefixWord ++ tailWord_7577074).sum := by decide
  have hdescent : baseEnd_7577074 < baseStart_7577074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577117 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_7577117 : Nat := 118140960795 + 7577117 * 2 ^ 59
def prefixEnd_7577117 : Nat := 4983230072969 + 3 ^ 40 * 7577117 * 2
def baseEnd_7577117 : Nat := 1296900998784512076196993

theorem tailTrace_7577117 : CollatzResearch.WordTrace tailWord_7577117 prefixEnd_7577117 1296900998784512076196993 := by
  unfold tailWord_7577117
  simp only [CollatzResearch.WordTrace]
  refine ⟨276360160890406652402649605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184240107260271101601766403 276360160890406652402649605)
  ·
    refine ⟨51817530166951247325496801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276360160890406652402649605 51817530166951247325496801)
    ·
      refine ⟨38863147625213435494122601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51817530166951247325496801 38863147625213435494122601)
      ·
        refine ⟨29147360718910076620591951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38863147625213435494122601 29147360718910076620591951)
        ·
          refine ⟨43721041078365114930887927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29147360718910076620591951 43721041078365114930887927)
          ·
            refine ⟨65581561617547672396331891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43721041078365114930887927 65581561617547672396331891)
            ·
              refine ⟨98372342426321508594497837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65581561617547672396331891 98372342426321508594497837)
              ·
                refine ⟨36889628409870565722936689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98372342426321508594497837 36889628409870565722936689)
                ·
                  refine ⟨27667221307402924292202517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36889628409870565722936689 27667221307402924292202517)
                  ·
                    refine ⟨1296900998784512076196993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27667221307402924292202517 1296900998784512076196993)
                    ·
                      rfl

theorem cell23_7577117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_7577117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577117 prefixEnd_7577117 := by exact prefixLift 7577117
  have htrace : WordTrace (prefixWord ++ tailWord_7577117) baseStart_7577117 baseEnd_7577117 := by
    simpa [prefixWord, tailWord_7577117, baseEnd_7577117] using wordTrace_append hprefix tailTrace_7577117
  have hstable : (prefixWord ++ tailWord_7577117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577117).length < 2 ^ (prefixWord ++ tailWord_7577117).sum := by decide
  have hdescent : baseEnd_7577117 < baseStart_7577117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577141 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_7577141 : Nat := 118140960795 + 7577141 * 2 ^ 59
def prefixEnd_7577141 : Nat := 4983230072969 + 3 ^ 40 * 7577141 * 2
def baseEnd_7577141 : Nat := 3890715319889244134690869

theorem tailTrace_7577141 : CollatzResearch.WordTrace tailWord_7577141 prefixEnd_7577141 3890715319889244134690869 := by
  unfold tailWord_7577141
  simp only [CollatzResearch.WordTrace]
  refine ⟨276361036242319704501523277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184240690828213136334348851 276361036242319704501523277)
  ·
    refine ⟨103635388590869889188071229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 276361036242319704501523277 103635388590869889188071229)
    ·
      refine ⟨38863270721576208445526711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103635388590869889188071229 38863270721576208445526711)
      ·
        refine ⟨58294906082364312668290067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38863270721576208445526711 58294906082364312668290067)
        ·
          refine ⟨87442359123546469002435101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58294906082364312668290067 87442359123546469002435101)
          ·
            refine ⟨32790884671329925875913163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87442359123546469002435101 32790884671329925875913163)
            ·
              refine ⟨49186327006994888813869745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32790884671329925875913163 49186327006994888813869745)
              ·
                refine ⟨36889745255246166610402309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49186327006994888813869745 36889745255246166610402309)
                ·
                  refine ⟨6916827235358656239450433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36889745255246166610402309 6916827235358656239450433)
                  ·
                    refine ⟨5187620426518992179587825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6916827235358656239450433 5187620426518992179587825)
                    ·
                      refine ⟨3890715319889244134690869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5187620426518992179587825 3890715319889244134690869)
                      ·
                        rfl

theorem cell23_7577141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_7577141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577141 prefixEnd_7577141 := by exact prefixLift 7577141
  have htrace : WordTrace (prefixWord ++ tailWord_7577141) baseStart_7577141 baseEnd_7577141 := by
    simpa [prefixWord, tailWord_7577141, baseEnd_7577141] using wordTrace_append hprefix tailTrace_7577141
  have hstable : (prefixWord ++ tailWord_7577141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577141).length < 2 ^ (prefixWord ++ tailWord_7577141).sum := by decide
  have hdescent : baseEnd_7577141 < baseStart_7577141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577164 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 7]
def baseStart_7577164 : Nat := 118140960795 + 7577164 * 2 ^ 59
def prefixEnd_7577164 : Nat := 4983230072969 + 3 ^ 40 * 7577164 * 2
def baseEnd_7577164 : Nat := 432303014438255282744807

theorem tailTrace_7577164 : CollatzResearch.WordTrace tailWord_7577164 prefixEnd_7577164 432303014438255282744807 := by
  unfold tailWord_7577164
  simp only [CollatzResearch.WordTrace]
  refine ⟨138180937560618189714805273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184241250080824252953073697 138180937560618189714805273)
  ·
    refine ⟨103635703170463642286103955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138180937560618189714805273 103635703170463642286103955)
    ·
      refine ⟨155453554755695463429155933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103635703170463642286103955 155453554755695463429155933)
      ·
        refine ⟨58295083033385798785933475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155453554755695463429155933 58295083033385798785933475)
        ·
          refine ⟨87442624550078698178900213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58295083033385798785933475 87442624550078698178900213)
          ·
            refine ⟨8197746051569877954271895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87442624550078698178900213 8197746051569877954271895)
            ·
              refine ⟨12296619077354816931407843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197746051569877954271895 12296619077354816931407843)
              ·
                refine ⟨18444928616032225397111765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12296619077354816931407843 18444928616032225397111765)
                ·
                  refine ⟨432303014438255282744807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18444928616032225397111765 432303014438255282744807)
                  ·
                    rfl

theorem cell23_7577164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_7577164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577164 prefixEnd_7577164 := by exact prefixLift 7577164
  have htrace : WordTrace (prefixWord ++ tailWord_7577164) baseStart_7577164 baseEnd_7577164 := by
    simpa [prefixWord, tailWord_7577164, baseEnd_7577164] using wordTrace_append hprefix tailTrace_7577164
  have hstable : (prefixWord ++ tailWord_7577164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577164).length < 2 ^ (prefixWord ++ tailWord_7577164).sum := by decide
  have hdescent : baseEnd_7577164 < baseStart_7577164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577175 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 2, 2, 2]
def baseStart_7577175 : Nat := 118140960795 + 7577175 * 2 ^ 59
def prefixEnd_7577175 : Nat := 4983230072969 + 3 ^ 40 * 7577175 * 2
def baseEnd_7577175 : Nat := 3890732778231497001665713

theorem tailTrace_7577175 : CollatzResearch.WordTrace tailWord_7577175 prefixEnd_7577175 3890732778231497001665713 := by
  unfold tailWord_7577175
  simp only [CollatzResearch.WordTrace]
  refine ⟨276362276324196528308260979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184241517549464352205507319 276362276324196528308260979)
  ·
    refine ⟨414543414486294792462391469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276362276324196528308260979 414543414486294792462391469)
    ·
      refine ⟨155453780432360547173396801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414543414486294792462391469 155453780432360547173396801)
      ·
        refine ⟨116590335324270410380047601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155453780432360547173396801 116590335324270410380047601)
        ·
          refine ⟨87442751493202807785035701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116590335324270410380047601 87442751493202807785035701)
          ·
            refine ⟨8197757952487763229847097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87442751493202807785035701 8197757952487763229847097)
            ·
              refine ⟨6148318464365822422385323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8197757952487763229847097 6148318464365822422385323)
              ·
                refine ⟨9222477696548733633577985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148318464365822422385323 9222477696548733633577985)
                ·
                  refine ⟨6916858272411550225183489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222477696548733633577985 6916858272411550225183489)
                  ·
                    refine ⟨5187643704308662668887617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6916858272411550225183489 5187643704308662668887617)
                    ·
                      refine ⟨3890732778231497001665713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5187643704308662668887617 3890732778231497001665713)
                      ·
                        rfl

theorem cell23_7577175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_7577175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577175 prefixEnd_7577175 := by exact prefixLift 7577175
  have htrace : WordTrace (prefixWord ++ tailWord_7577175) baseStart_7577175 baseEnd_7577175 := by
    simpa [prefixWord, tailWord_7577175, baseEnd_7577175] using wordTrace_append hprefix tailTrace_7577175
  have hstable : (prefixWord ++ tailWord_7577175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577175).length < 2 ^ (prefixWord ++ tailWord_7577175).sum := by decide
  have hdescent : baseEnd_7577175 < baseStart_7577175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577194 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_7577194 : Nat := 118140960795 + 7577194 * 2 ^ 59
def prefixEnd_7577194 : Nat := 4983230072969 + 3 ^ 40 * 7577194 * 2
def baseEnd_7577194 : Nat := 1296914178121310809109375

theorem tailTrace_7577194 : CollatzResearch.WordTrace tailWord_7577194 prefixEnd_7577194 1296914178121310809109375 := by
  unfold tailWord_7577194
  simp only [CollatzResearch.WordTrace]
  refine ⟨69090742327781923638300659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184241979540751796368801757 69090742327781923638300659)
  ·
    refine ⟨103636113491672885457450989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69090742327781923638300659 103636113491672885457450989)
    ·
      refine ⟨38863542559377332046544121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103636113491672885457450989 38863542559377332046544121)
      ·
        refine ⟨29147656919532999034908091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38863542559377332046544121 29147656919532999034908091)
        ·
          refine ⟨43721485379299498552362137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29147656919532999034908091 43721485379299498552362137)
          ·
            refine ⟨32791114034474623914271603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43721485379299498552362137 32791114034474623914271603)
            ·
              refine ⟨49186671051711935871407405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32791114034474623914271603 49186671051711935871407405)
              ·
                refine ⟨18445001644391975951777777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49186671051711935871407405 18445001644391975951777777)
                ·
                  refine ⟨13833751233293981963833333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18445001644391975951777777 13833751233293981963833333)
                  ·
                    refine ⟨1296914178121310809109375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13833751233293981963833333 1296914178121310809109375)
                    ·
                      rfl

theorem cell23_7577194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_7577194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577194 prefixEnd_7577194 := by exact prefixLift 7577194
  have htrace : WordTrace (prefixWord ++ tailWord_7577194) baseStart_7577194 baseEnd_7577194 := by
    simpa [prefixWord, tailWord_7577194, baseEnd_7577194] using wordTrace_append hprefix tailTrace_7577194
  have hstable : (prefixWord ++ tailWord_7577194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577194).length < 2 ^ (prefixWord ++ tailWord_7577194).sum := by decide
  have hdescent : baseEnd_7577194 < baseStart_7577194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577271 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 6]
def baseStart_7577271 : Nat := 118140960795 + 7577271 * 2 ^ 59
def prefixEnd_7577271 : Nat := 4983230072969 + 3 ^ 40 * 7577271 * 2
def baseEnd_7577271 : Nat := 432309119152703180673919

theorem tailTrace_7577271 : CollatzResearch.WordTrace tailWord_7577271 prefixEnd_7577271 432309119152703180673919 := by
  unfold tailWord_7577271
  simp only [CollatzResearch.WordTrace]
  refine ⟨276365777731848736703755667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184243851821232491135837111 276365777731848736703755667)
  ·
    refine ⟨414548666597773105055633501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276365777731848736703755667 414548666597773105055633501)
    ·
      refine ⟨155455749974164914395862563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 414548666597773105055633501 155455749974164914395862563)
      ·
        refine ⟨233183624961247371593793845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155455749974164914395862563 233183624961247371593793845)
        ·
          refine ⟨21860964840116941086918173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233183624961247371593793845 21860964840116941086918173)
          ·
            refine ⟨8197861815043852907594315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21860964840116941086918173 8197861815043852907594315)
            ·
              refine ⟨12296792722565779361391473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197861815043852907594315 12296792722565779361391473)
              ·
                refine ⟨9222594541924334521043605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12296792722565779361391473 9222594541924334521043605)
                ·
                  refine ⟨432309119152703180673919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9222594541924334521043605 432309119152703180673919)
                  ·
                    rfl

theorem cell23_7577271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 6].length) (baseStart_7577271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577271 prefixEnd_7577271 := by exact prefixLift 7577271
  have htrace : WordTrace (prefixWord ++ tailWord_7577271) baseStart_7577271 baseEnd_7577271 := by
    simpa [prefixWord, tailWord_7577271, baseEnd_7577271] using wordTrace_append hprefix tailTrace_7577271
  have hstable : (prefixWord ++ tailWord_7577271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577271).length < 2 ^ (prefixWord ++ tailWord_7577271).sum := by decide
  have hdescent : baseEnd_7577271 < baseStart_7577271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577298 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_7577298 : Nat := 118140960795 + 7577298 * 2 ^ 59
def prefixEnd_7577298 : Nat := 4983230072969 + 3 ^ 40 * 7577298 * 2
def baseEnd_7577298 : Nat := 3890795936352000020427647

theorem tailTrace_7577298 : CollatzResearch.WordTrace tailWord_7577298 prefixEnd_7577298 3890795936352000020427647 := by
  unfold tailWord_7577298
  simp only [CollatzResearch.WordTrace]
  refine ⟨69091690625687730078747137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184244508335167280209992365 69091690625687730078747137)
  ·
    refine ⟨51818767969265797559060353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69091690625687730078747137 51818767969265797559060353)
    ·
      refine ⟨38864075976949348169295265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51818767969265797559060353 38864075976949348169295265)
      ·
        refine ⟨29148056982712011126971449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38864075976949348169295265 29148056982712011126971449)
        ·
          refine ⟨21861042737034008345228587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29148056982712011126971449 21861042737034008345228587)
          ·
            refine ⟨32791564105551012517842881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21861042737034008345228587 32791564105551012517842881)
            ·
              refine ⟨24593673079163259388382161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32791564105551012517842881 24593673079163259388382161)
              ·
                refine ⟨18445254809372444541286621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24593673079163259388382161 18445254809372444541286621)
                ·
                  refine ⟨6916970553514666702982483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18445254809372444541286621 6916970553514666702982483)
                  ·
                    refine ⟨10375455830272000054473725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6916970553514666702982483 10375455830272000054473725)
                    ·
                      refine ⟨3890795936352000020427647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10375455830272000054473725 3890795936352000020427647)
                      ·
                        rfl

theorem cell23_7577298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_7577298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577298 prefixEnd_7577298 := by exact prefixLift 7577298
  have htrace : WordTrace (prefixWord ++ tailWord_7577298) baseStart_7577298 baseEnd_7577298 := by
    simpa [prefixWord, tailWord_7577298, baseEnd_7577298] using wordTrace_append hprefix tailTrace_7577298
  have hstable : (prefixWord ++ tailWord_7577298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577298).length < 2 ^ (prefixWord ++ tailWord_7577298).sum := by decide
  have hdescent : baseEnd_7577298 < baseStart_7577298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577307 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5]
def baseStart_7577307 : Nat := 118140960795 + 7577307 * 2 ^ 59
def prefixEnd_7577307 : Nat := 4983230072969 + 3 ^ 40 * 7577307 * 2
def baseEnd_7577307 : Nat := 3890800557677890485215105

theorem tailTrace_7577307 : CollatzResearch.WordTrace tailWord_7577307 prefixEnd_7577307 3890800557677890485215105 := by
  unfold tailWord_7577307
  simp only [CollatzResearch.WordTrace]
  refine ⟨276367090759718314852066175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184244727173145543234710783 276367090759718314852066175)
  ·
    refine ⟨414550636139577472278099263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276367090759718314852066175 414550636139577472278099263)
    ·
      refine ⟨621825954209366208417148895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414550636139577472278099263 621825954209366208417148895)
      ·
        refine ⟨932738931314049312625723343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621825954209366208417148895 932738931314049312625723343)
        ·
          refine ⟨1399108396971073968938585015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932738931314049312625723343 1399108396971073968938585015)
          ·
            refine ⟨2098662595456610953407877523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1399108396971073968938585015 2098662595456610953407877523)
            ·
              refine ⟨3147993893184916430111816285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098662595456610953407877523 3147993893184916430111816285)
              ·
                refine ⟨1180497709944343661291931107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3147993893184916430111816285 1180497709944343661291931107)
                ·
                  refine ⟨1770746564916515491937896661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1180497709944343661291931107 1770746564916515491937896661)
                  ·
                    refine ⟨41501872615230831842294453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1770746564916515491937896661 41501872615230831842294453)
                    ·
                      refine ⟨3890800557677890485215105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41501872615230831842294453 3890800557677890485215105)
                      ·
                        rfl

theorem cell23_7577307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_7577307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577307 prefixEnd_7577307 := by exact prefixLift 7577307
  have htrace : WordTrace (prefixWord ++ tailWord_7577307) baseStart_7577307 baseEnd_7577307 := by
    simpa [prefixWord, tailWord_7577307, baseEnd_7577307] using wordTrace_append hprefix tailTrace_7577307
  have hstable : (prefixWord ++ tailWord_7577307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577307).length < 2 ^ (prefixWord ++ tailWord_7577307).sum := by decide
  have hdescent : baseEnd_7577307 < baseStart_7577307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577309 : List Nat := [1, 4, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_7577309 : Nat := 118140960795 + 7577309 * 2 ^ 59
def prefixEnd_7577309 : Nat := 4983230072969 + 3 ^ 40 * 7577309 * 2
def baseEnd_7577309 : Nat := 1296933861546399825796699

theorem tailTrace_7577309 : CollatzResearch.WordTrace tailWord_7577309 prefixEnd_7577309 1296933861546399825796699 := by
  unfold tailWord_7577309
  simp only [CollatzResearch.WordTrace]
  refine ⟨276367163705711069193638981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184244775803807379462425987 276367163705711069193638981)
  ·
    refine ⟨51818843194820825473807309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276367163705711069193638981 51818843194820825473807309)
    ·
      refine ⟨19432066198057809552677741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51818843194820825473807309 19432066198057809552677741)
      ·
        refine ⟨7287024824271678582254153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19432066198057809552677741 7287024824271678582254153)
        ·
          refine ⟨5465268618203758936690615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7287024824271678582254153 5465268618203758936690615)
          ·
            refine ⟨8197902927305638405035923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465268618203758936690615 8197902927305638405035923)
            ·
              refine ⟨12296854390958457607553885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197902927305638405035923 12296854390958457607553885)
              ·
                refine ⟨4611320396609421602832707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12296854390958457607553885 4611320396609421602832707)
                ·
                  refine ⟨6916980594914132404249061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4611320396609421602832707 6916980594914132404249061)
                  ·
                    refine ⟨1296933861546399825796699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916980594914132404249061 1296933861546399825796699)
                    ·
                      rfl

theorem cell23_7577309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_7577309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577309 prefixEnd_7577309 := by exact prefixLift 7577309
  have htrace : WordTrace (prefixWord ++ tailWord_7577309) baseStart_7577309 baseEnd_7577309 := by
    simpa [prefixWord, tailWord_7577309, baseEnd_7577309] using wordTrace_append hprefix tailTrace_7577309
  have hstable : (prefixWord ++ tailWord_7577309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577309).length < 2 ^ (prefixWord ++ tailWord_7577309).sum := by decide
  have hdescent : baseEnd_7577309 < baseStart_7577309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577324 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_7577324 : Nat := 118140960795 + 7577324 * 2 ^ 59
def prefixEnd_7577324 : Nat := 4983230072969 + 3 ^ 40 * 7577324 * 2
def baseEnd_7577324 : Nat := 3890809286849016918702527

theorem tailTrace_7577324 : CollatzResearch.WordTrace tailWord_7577324 prefixEnd_7577324 3890809286849016918702527 := by
  unfold tailWord_7577324
  simp only [CollatzResearch.WordTrace]
  refine ⟨138183855400328363377717513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184245140533771151170290017 138183855400328363377717513)
  ·
    refine ⟨103637891550246272533288135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138183855400328363377717513 103637891550246272533288135)
    ·
      refine ⟨155456837325369408799932203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103637891550246272533288135 155456837325369408799932203)
      ·
        refine ⟨233185255988054113199898305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155456837325369408799932203 233185255988054113199898305)
        ·
          refine ⟨174888941991040584899923729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233185255988054113199898305 174888941991040584899923729)
          ·
            refine ⟨131166706493280438674942797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174888941991040584899923729 131166706493280438674942797)
            ·
              refine ⟨49187514934980164503103549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131166706493280438674942797 49187514934980164503103549)
              ·
                refine ⟨18445318100617561688663831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49187514934980164503103549 18445318100617561688663831)
                ·
                  refine ⟨27667977150926342532995747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18445318100617561688663831 27667977150926342532995747)
                  ·
                    refine ⟨41501965726389513799493621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27667977150926342532995747 41501965726389513799493621)
                    ·
                      refine ⟨3890809286849016918702527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41501965726389513799493621 3890809286849016918702527)
                      ·
                        rfl

theorem cell23_7577324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_7577324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577324 prefixEnd_7577324 := by exact prefixLift 7577324
  have htrace : WordTrace (prefixWord ++ tailWord_7577324) baseStart_7577324 baseEnd_7577324 := by
    simpa [prefixWord, tailWord_7577324, baseEnd_7577324] using wordTrace_append hprefix tailTrace_7577324
  have hstable : (prefixWord ++ tailWord_7577324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577324).length < 2 ^ (prefixWord ++ tailWord_7577324).sum := by decide
  have hdescent : baseEnd_7577324 < baseStart_7577324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577332 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7577332 : Nat := 118140960795 + 7577332 * 2 ^ 59
def prefixEnd_7577332 : Nat := 4983230072969 + 3 ^ 40 * 7577332 * 2
def baseEnd_7577332 : Nat := 3890813394694252887402491

theorem tailTrace_7577332 : CollatzResearch.WordTrace tailWord_7577332 prefixEnd_7577332 3890813394694252887402491 := by
  unfold tailWord_7577332
  simp only [CollatzResearch.WordTrace]
  refine ⟨138184001292313872060863125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184245335056418496081150833 138184001292313872060863125)
  ·
    refine ⟨6477375060577212752852959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138184001292313872060863125 6477375060577212752852959)
    ·
      refine ⟨9716062590865819129279439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6477375060577212752852959 9716062590865819129279439)
      ·
        refine ⟨14574093886298728693919159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9716062590865819129279439 14574093886298728693919159)
        ·
          refine ⟨21861140829448093040878739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14574093886298728693919159 21861140829448093040878739)
          ·
            refine ⟨32791711244172139561318109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21861140829448093040878739 32791711244172139561318109)
            ·
              refine ⟨12296891716564552335494291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32791711244172139561318109 12296891716564552335494291)
              ·
                refine ⟨18445337574846828503241437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12296891716564552335494291 18445337574846828503241437)
                ·
                  refine ⟨6917001590567560688715539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18445337574846828503241437 6917001590567560688715539)
                  ·
                    refine ⟨10375502385851341033073309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6917001590567560688715539 10375502385851341033073309)
                    ·
                      refine ⟨3890813394694252887402491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10375502385851341033073309 3890813394694252887402491)
                      ·
                        rfl

theorem cell23_7577332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7577332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577332 prefixEnd_7577332 := by exact prefixLift 7577332
  have htrace : WordTrace (prefixWord ++ tailWord_7577332) baseStart_7577332 baseEnd_7577332 := by
    simpa [prefixWord, tailWord_7577332, baseEnd_7577332] using wordTrace_append hprefix tailTrace_7577332
  have hstable : (prefixWord ++ tailWord_7577332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577332).length < 2 ^ (prefixWord ++ tailWord_7577332).sum := by decide
  have hdescent : baseEnd_7577332 < baseStart_7577332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577348 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_7577348 : Nat := 118140960795 + 7577348 * 2 ^ 59
def prefixEnd_7577348 : Nat := 4983230072969 + 3 ^ 40 * 7577348 * 2
def baseEnd_7577348 : Nat := 1296940536794908274934139

theorem tailTrace_7577348 : CollatzResearch.WordTrace tailWord_7577348 prefixEnd_7577348 1296940536794908274934139 := by
  unfold tailWord_7577348
  simp only [CollatzResearch.WordTrace]
  refine ⟨138184293076284889427154349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184245724101713185902872465 138184293076284889427154349)
  ·
    refine ⟨51819109903606833535182881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138184293076284889427154349 51819109903606833535182881)
    ·
      refine ⟨38864332427705125151387161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51819109903606833535182881 38864332427705125151387161)
      ·
        refine ⟨29148249320778843863540371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38864332427705125151387161 29148249320778843863540371)
        ·
          refine ⟨43722373981168265795310557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29148249320778843863540371 43722373981168265795310557)
          ·
            refine ⟨16395890242938099673241459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43722373981168265795310557 16395890242938099673241459)
            ·
              refine ⟨24593835364407149509862189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16395890242938099673241459 24593835364407149509862189)
              ·
                refine ⟨9222688261652681066198321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24593835364407149509862189 9222688261652681066198321)
                ·
                  refine ⟨6917016196239510799648741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222688261652681066198321 6917016196239510799648741)
                  ·
                    refine ⟨1296940536794908274934139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6917016196239510799648741 1296940536794908274934139)
                    ·
                      rfl

theorem cell23_7577348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_7577348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577348 prefixEnd_7577348 := by exact prefixLift 7577348
  have htrace : WordTrace (prefixWord ++ tailWord_7577348) baseStart_7577348 baseEnd_7577348 := by
    simpa [prefixWord, tailWord_7577348, baseEnd_7577348] using wordTrace_append hprefix tailTrace_7577348
  have hstable : (prefixWord ++ tailWord_7577348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577348).length < 2 ^ (prefixWord ++ tailWord_7577348).sum := by decide
  have hdescent : baseEnd_7577348 < baseStart_7577348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577358 : List Nat := [4, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_7577358 : Nat := 118140960795 + 7577358 * 2 ^ 59
def prefixEnd_7577358 : Nat := 4983230072969 + 3 ^ 40 * 7577358 * 2
def baseEnd_7577358 : Nat := 3890826745191269785677371

theorem tailTrace_7577358 : CollatzResearch.WordTrace tailWord_7577358 prefixEnd_7577358 3890826745191269785677371 := by
  unfold tailWord_7577358
  simp only [CollatzResearch.WordTrace]
  refine ⟨34546118860316693820271591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184245967255022367041448485 34546118860316693820271591)
  ·
    refine ⟨51819178290475040730407387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34546118860316693820271591 51819178290475040730407387)
    ·
      refine ⟨77728767435712561095611081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51819178290475040730407387 77728767435712561095611081)
      ·
        refine ⟨58296575576784420821708311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77728767435712561095611081 58296575576784420821708311)
        ·
          refine ⟨87444863365176631232562467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58296575576784420821708311 87444863365176631232562467)
          ·
            refine ⟨131167295047764946848843701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87444863365176631232562467 131167295047764946848843701)
            ·
              refine ⟨12296933910727963767079097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131167295047764946848843701 12296933910727963767079097)
              ·
                refine ⟨9222700433045972825309323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12296933910727963767079097 9222700433045972825309323)
                ·
                  refine ⟨13834050649568959237963985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9222700433045972825309323 13834050649568959237963985)
                  ·
                    refine ⟨10375537987176719428472989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13834050649568959237963985 10375537987176719428472989)
                    ·
                      refine ⟨3890826745191269785677371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10375537987176719428472989 3890826745191269785677371)
                      ·
                        rfl

theorem cell23_7577358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_7577358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577358 prefixEnd_7577358 := by exact prefixLift 7577358
  have htrace : WordTrace (prefixWord ++ tailWord_7577358) baseStart_7577358 baseEnd_7577358 := by
    simpa [prefixWord, tailWord_7577358, baseEnd_7577358] using wordTrace_append hprefix tailTrace_7577358
  have hstable : (prefixWord ++ tailWord_7577358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577358).length < 2 ^ (prefixWord ++ tailWord_7577358).sum := by decide
  have hdescent : baseEnd_7577358 < baseStart_7577358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577388 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 3]
def baseStart_7577388 : Nat := 118140960795 + 7577388 * 2 ^ 59
def prefixEnd_7577388 : Nat := 4983230072969 + 3 ^ 40 * 7577388 * 2
def baseEnd_7577388 : Nat := 3890842149610904668302233

theorem tailTrace_7577388 : CollatzResearch.WordTrace tailWord_7577388 prefixEnd_7577388 3890842149610904668302233 := by
  unfold tailWord_7577388
  simp only [CollatzResearch.WordTrace]
  refine ⟨138185022536212432842882409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184246696714949910457176545 138185022536212432842882409)
  ·
    refine ⟨103638766902159324632161807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138185022536212432842882409 103638766902159324632161807)
    ·
      refine ⟨155458150353238986948242711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103638766902159324632161807 155458150353238986948242711)
      ·
        refine ⟨233187225529858480422364067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155458150353238986948242711 233187225529858480422364067)
        ·
          refine ⟨349780838294787720633546101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233187225529858480422364067 349780838294787720633546101)
          ·
            refine ⟨32791953590136348809394947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349780838294787720633546101 32791953590136348809394947)
            ·
              refine ⟨49187930385204523214092421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32791953590136348809394947 49187930385204523214092421)
              ·
                refine ⟨9222736947225848102642329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49187930385204523214092421 9222736947225848102642329)
                ·
                  refine ⟨6917052710419386076981747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222736947225848102642329 6917052710419386076981747)
                  ·
                    refine ⟨10375579065629079115472621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6917052710419386076981747 10375579065629079115472621)
                    ·
                      refine ⟨3890842149610904668302233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10375579065629079115472621 3890842149610904668302233)
                      ·
                        rfl

theorem cell23_7577388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_7577388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577388 prefixEnd_7577388 := by exact prefixLift 7577388
  have htrace : WordTrace (prefixWord ++ tailWord_7577388) baseStart_7577388 baseEnd_7577388 := by
    simpa [prefixWord, tailWord_7577388, baseEnd_7577388] using wordTrace_append hprefix tailTrace_7577388
  have hstable : (prefixWord ++ tailWord_7577388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577388).length < 2 ^ (prefixWord ++ tailWord_7577388).sum := by decide
  have hdescent : baseEnd_7577388 < baseStart_7577388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577404 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_7577404 : Nat := 118140960795 + 7577404 * 2 ^ 59
def prefixEnd_7577404 : Nat := 4983230072969 + 3 ^ 40 * 7577404 * 2
def baseEnd_7577404 : Nat := 1296950121767125535234053

theorem tailTrace_7577404 : CollatzResearch.WordTrace tailWord_7577404 prefixEnd_7577404 1296950121767125535234053 := by
  unfold tailWord_7577404
  simp only [CollatzResearch.WordTrace]
  refine ⟨138185314320183450209173633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184247085760244600278898177 138185314320183450209173633)
  ·
    refine ⟨103638985740137587656880225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138185314320183450209173633 103638985740137587656880225)
    ·
      refine ⟨77729239305103190742660169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103638985740137587656880225 77729239305103190742660169)
      ·
        refine ⟨58296929478827393056995127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77729239305103190742660169 58296929478827393056995127)
        ·
          refine ⟨87445394218241089585492691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58296929478827393056995127 87445394218241089585492691)
          ·
            refine ⟨131168091327361634378239037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87445394218241089585492691 131168091327361634378239037)
            ·
              refine ⟨49188034247760612891839639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131168091327361634378239037 49188034247760612891839639)
              ·
                refine ⟨73782051371640919337759459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49188034247760612891839639 73782051371640919337759459)
                ·
                  refine ⟨110673077057461379006639189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73782051371640919337759459 110673077057461379006639189)
                  ·
                    refine ⟨1296950121767125535234053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110673077057461379006639189 1296950121767125535234053)
                    ·
                      rfl

theorem cell23_7577404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_7577404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577404 prefixEnd_7577404 := by exact prefixLift 7577404
  have htrace : WordTrace (prefixWord ++ tailWord_7577404) baseStart_7577404 baseEnd_7577404 := by
    simpa [prefixWord, tailWord_7577404, baseEnd_7577404] using wordTrace_append hprefix tailTrace_7577404
  have hstable : (prefixWord ++ tailWord_7577404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577404).length < 2 ^ (prefixWord ++ tailWord_7577404).sum := by decide
  have hdescent : baseEnd_7577404 < baseStart_7577404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577405 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_7577405 : Nat := 118140960795 + 7577405 * 2 ^ 59
def prefixEnd_7577405 : Nat := 4983230072969 + 3 ^ 40 * 7577405 * 2
def baseEnd_7577405 : Nat := 3890850878782031101789655

theorem tailTrace_7577405 : CollatzResearch.WordTrace tailWord_7577405 prefixEnd_7577405 3890850878782031101789655 := by
  unfold tailWord_7577405
  simp only [CollatzResearch.WordTrace]
  refine ⟨276370665113363277589133669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184247110075575518392755779 276370665113363277589133669)
  ·
    refine ⟨51819499708755614547962563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 276370665113363277589133669 51819499708755614547962563)
    ·
      refine ⟨77729249563133421821943845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51819499708755614547962563 77729249563133421821943845)
      ·
        refine ⟨14574234293087516591614471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77729249563133421821943845 14574234293087516591614471)
        ·
          refine ⟨21861351439631274887421707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14574234293087516591614471 21861351439631274887421707)
          ·
            refine ⟨32792027159446912331132561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21861351439631274887421707 32792027159446912331132561)
            ·
              refine ⟨24594020369585184248349421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32792027159446912331132561 24594020369585184248349421)
              ·
                refine ⟨9222757638594444093131033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24594020369585184248349421 9222757638594444093131033)
                ·
                  refine ⟨6917068228945833069848275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222757638594444093131033 6917068228945833069848275)
                  ·
                    refine ⟨10375602343418749604772413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6917068228945833069848275 10375602343418749604772413)
                    ·
                      refine ⟨3890850878782031101789655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10375602343418749604772413 3890850878782031101789655)
                      ·
                        rfl

theorem cell23_7577405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_7577405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577405 prefixEnd_7577405 := by exact prefixLift 7577405
  have htrace : WordTrace (prefixWord ++ tailWord_7577405) baseStart_7577405 baseEnd_7577405 := by
    simpa [prefixWord, tailWord_7577405, baseEnd_7577405] using wordTrace_append hprefix tailTrace_7577405
  have hstable : (prefixWord ++ tailWord_7577405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577405).length < 2 ^ (prefixWord ++ tailWord_7577405).sum := by decide
  have hdescent : baseEnd_7577405 < baseStart_7577405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577424 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 4]
def baseStart_7577424 : Nat := 118140960795 + 7577424 * 2 ^ 59
def prefixEnd_7577424 : Nat := 4983230072969 + 3 ^ 40 * 7577424 * 2
def baseEnd_7577424 : Nat := 3890860634914466527452067

theorem tailTrace_7577424 : CollatzResearch.WordTrace tailWord_7577424 prefixEnd_7577424 3890860634914466527452067 := by
  unfold tailWord_7577424
  simp only [CollatzResearch.WordTrace]
  refine ⟨138185679050147221917037663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184247572066862962556050217 138185679050147221917037663)
  ·
    refine ⟨207278518575220832875556495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138185679050147221917037663 207278518575220832875556495)
    ·
      refine ⟨310917777862831249313334743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207278518575220832875556495 310917777862831249313334743)
      ·
        refine ⟨466376666794246873970002115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310917777862831249313334743 466376666794246873970002115)
        ·
          refine ⟨699565000191370310955003173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466376666794246873970002115 699565000191370310955003173)
          ·
            refine ⟨131168437535881933304063095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 699565000191370310955003173 131168437535881933304063095)
            ·
              refine ⟨196752656303822899956094643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131168437535881933304063095 196752656303822899956094643)
              ·
                refine ⟨295128984455734349934141965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196752656303822899956094643 295128984455734349934141965)
                ·
                  refine ⟨110673369170900381225303237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295128984455734349934141965 110673369170900381225303237)
                  ·
                    refine ⟨20751256719543821479744357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110673369170900381225303237 20751256719543821479744357)
                    ·
                      refine ⟨3890860634914466527452067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20751256719543821479744357 3890860634914466527452067)
                      ·
                        rfl

theorem cell23_7577424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_7577424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577424 prefixEnd_7577424 := by exact prefixLift 7577424
  have htrace : WordTrace (prefixWord ++ tailWord_7577424) baseStart_7577424 baseEnd_7577424 := by
    simpa [prefixWord, tailWord_7577424, baseEnd_7577424] using wordTrace_append hprefix tailTrace_7577424
  have hstable : (prefixWord ++ tailWord_7577424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577424).length < 2 ^ (prefixWord ++ tailWord_7577424).sum := by decide
  have hdescent : baseEnd_7577424 < baseStart_7577424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577434 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 9]
def baseStart_7577434 : Nat := 118140960795 + 7577434 * 2 ^ 59
def prefixEnd_7577434 : Nat := 4983230072969 + 3 ^ 40 * 7577434 * 2
def baseEnd_7577434 : Nat := 432318418857890165369669

theorem tailTrace_7577434 : CollatzResearch.WordTrace tailWord_7577434 prefixEnd_7577434 432318418857890165369669 := by
  unfold tailWord_7577434
  simp only [CollatzResearch.WordTrace]
  refine ⟨69092930707564553885484839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184247815220172143694626237 69092930707564553885484839)
  ·
    refine ⟨103639396061346830828227259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69092930707564553885484839 103639396061346830828227259)
    ·
      refine ⟨155459094092020246242340889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103639396061346830828227259 155459094092020246242340889)
      ·
        refine ⟨116594320569015184681755667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155459094092020246242340889 116594320569015184681755667)
        ·
          refine ⟨174891480853522777022633501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116594320569015184681755667 174891480853522777022633501)
          ·
            refine ⟨65584305320071041383487563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174891480853522777022633501 65584305320071041383487563)
            ·
              refine ⟨98376457980106562075231345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65584305320071041383487563 98376457980106562075231345)
              ·
                refine ⟨73782343485079921556423509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98376457980106562075231345 73782343485079921556423509)
                ·
                  refine ⟨432318418857890165369669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73782343485079921556423509 432318418857890165369669)
                  ·
                    rfl

theorem cell23_7577434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_7577434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577434 prefixEnd_7577434 := by exact prefixLift 7577434
  have htrace : WordTrace (prefixWord ++ tailWord_7577434) baseStart_7577434 baseEnd_7577434 := by
    simpa [prefixWord, tailWord_7577434, baseEnd_7577434] using wordTrace_append hprefix tailTrace_7577434
  have hstable : (prefixWord ++ tailWord_7577434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577434).length < 2 ^ (prefixWord ++ tailWord_7577434).sum := by decide
  have hdescent : baseEnd_7577434 < baseStart_7577434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577481 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 2, 5]
def baseStart_7577481 : Nat := 118140960795 + 7577481 * 2 ^ 59
def prefixEnd_7577481 : Nat := 4983230072969 + 3 ^ 40 * 7577481 * 2
def baseEnd_7577481 : Nat := 1296963301103924268146435

theorem tailTrace_7577481 : CollatzResearch.WordTrace tailWord_7577481 prefixEnd_7577481 1296963301103924268146435 := by
  unfold tailWord_7577481
  simp only [CollatzResearch.WordTrace]
  refine ⟨276373437061087942568900297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184248958040725295045933531 276373437061087942568900297)
  ·
    refine ⟨207280077795815956926675223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276373437061087942568900297 207280077795815956926675223)
    ·
      refine ⟨310920116693723935390012835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207280077795815956926675223 310920116693723935390012835)
      ·
        refine ⟨466380175040585903085019253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310920116693723935390012835 466380175040585903085019253)
        ·
          refine ⟨43723141410054928414220555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 466380175040585903085019253 43723141410054928414220555)
          ·
            refine ⟨65584712115082392621330833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43723141410054928414220555 65584712115082392621330833)
            ·
              refine ⟨49188534086311794465998125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65584712115082392621330833 49188534086311794465998125)
              ·
                refine ⟨18445700282366922924749297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49188534086311794465998125 18445700282366922924749297)
                ·
                  refine ⟨13834275211775192193561973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18445700282366922924749297 13834275211775192193561973)
                  ·
                    refine ⟨1296963301103924268146435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13834275211775192193561973 1296963301103924268146435)
                    ·
                      rfl

theorem cell23_7577481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_7577481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577481 prefixEnd_7577481 := by exact prefixLift 7577481
  have htrace : WordTrace (prefixWord ++ tailWord_7577481) baseStart_7577481 baseEnd_7577481 := by
    simpa [prefixWord, tailWord_7577481, baseEnd_7577481] using wordTrace_append hprefix tailTrace_7577481
  have hstable : (prefixWord ++ tailWord_7577481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577481).length < 2 ^ (prefixWord ++ tailWord_7577481).sum := by decide
  have hdescent : baseEnd_7577481 < baseStart_7577481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577498 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_7577498 : Nat := 118140960795 + 7577498 * 2 ^ 59
def prefixEnd_7577498 : Nat := 4983230072969 + 3 ^ 40 * 7577498 * 2
def baseEnd_7577498 : Nat := 1296966210827633079308909

theorem tailTrace_7577498 : CollatzResearch.WordTrace tailWord_7577498 prefixEnd_7577498 1296966210827633079308909 := by
  unfold tailWord_7577498
  simp only [CollatzResearch.WordTrace]
  refine ⟨69093514275506588618067287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184249371401350902981512765 69093514275506588618067287)
  ·
    refine ⟨103640271413259882927100931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69093514275506588618067287 103640271413259882927100931)
    ·
      refine ⟨155460407119889824390651397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103640271413259882927100931 155460407119889824390651397)
      ·
        refine ⟨29148826334979342073247137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155460407119889824390651397 29148826334979342073247137)
        ·
          refine ⟨21861619751234506554935353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29148826334979342073247137 21861619751234506554935353)
          ·
            refine ⟨16396214813425879916201515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21861619751234506554935353 16396214813425879916201515)
            ·
              refine ⟨24594322220138819874302273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16396214813425879916201515 24594322220138819874302273)
              ·
                refine ⟨18445741665104114905726705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24594322220138819874302273 18445741665104114905726705)
                ·
                  refine ⟨13834306248828086179295029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18445741665104114905726705 13834306248828086179295029)
                  ·
                    refine ⟨1296966210827633079308909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13834306248828086179295029 1296966210827633079308909)
                    ·
                      rfl

theorem cell23_7577498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_7577498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7577498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7577498 prefixEnd_7577498 := by exact prefixLift 7577498
  have htrace : WordTrace (prefixWord ++ tailWord_7577498) baseStart_7577498 baseEnd_7577498 := by
    simpa [prefixWord, tailWord_7577498, baseEnd_7577498] using wordTrace_append hprefix tailTrace_7577498
  have hstable : (prefixWord ++ tailWord_7577498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577498).length < 2 ^ (prefixWord ++ tailWord_7577498).sum := by decide
  have hdescent : baseEnd_7577498 < baseStart_7577498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
