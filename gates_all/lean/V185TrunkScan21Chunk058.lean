import V185TrunkScan21Chunk057

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_702007 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 7]
def baseStart_702007 : Nat := 118140960795 + 702007 * 2 ^ 59
def prefixEnd_702007 : Nat := 4983230072969 + 3 ^ 40 * 702007 * 2
def baseEnd_702007 : Nat := 160207561698195612481793

theorem tailTrace_702007 : CollatzResearch.WordTrace tailWord_702007 prefixEnd_702007 160207561698195612481793 := by
  unfold tailWord_702007
  simp only [CollatzResearch.WordTrace]
  refine ⟨25604298767756007095520275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17069532511837338063680183 25604298767756007095520275)
  ·
    refine ⟨38406448151634010643280413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25604298767756007095520275 38406448151634010643280413)
    ·
      refine ⟨14402418056862753991230155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38406448151634010643280413 14402418056862753991230155)
      ·
        refine ⟨21603627085294130986845233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14402418056862753991230155 21603627085294130986845233)
        ·
          refine ⟨16202720313970598240133925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21603627085294130986845233 16202720313970598240133925)
          ·
            refine ⟨3038010058869487170025111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16202720313970598240133925 3038010058869487170025111)
            ·
              refine ⟨4557015088304230755037667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3038010058869487170025111 4557015088304230755037667)
              ·
                refine ⟨6835522632456346132556501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557015088304230755037667 6835522632456346132556501)
                ·
                  refine ⟨160207561698195612481793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6835522632456346132556501 160207561698195612481793)
                  ·
                    rfl

theorem cell21_702007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_702007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702007 prefixEnd_702007 := by exact prefixLift 702007
  have htrace : WordTrace (prefixWord ++ tailWord_702007) baseStart_702007 baseEnd_702007 := by
    simpa [prefixWord, tailWord_702007, baseEnd_702007] using wordTrace_append hprefix tailTrace_702007
  have hstable : (prefixWord ++ tailWord_702007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702007).length < 2 ^ (prefixWord ++ tailWord_702007).sum := by decide
  have hdescent : baseEnd_702007 < baseStart_702007 := by decide
  rcases family_descends (prefixWord ++ tailWord_702007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702128 : List Nat := [2, 1, 1, 1, 2, 1, 6, 7]
def baseStart_702128 : Nat := 118140960795 + 702128 * 2 ^ 59
def prefixEnd_702128 : Nat := 4983230072969 + 3 ^ 40 * 702128 * 2
def baseEnd_702128 : Nat := 53411725182242096988293

theorem tailTrace_702128 : CollatzResearch.WordTrace tailWord_702128 prefixEnd_702128 53411725182242096988293 := by
  unfold tailWord_702128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12804356000158822380337519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17072474666878429840450025 12804356000158822380337519)
  ·
    refine ⟨19206534000238233570506279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12804356000158822380337519 19206534000238233570506279)
    ·
      refine ⟨28809801000357350355759419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19206534000238233570506279 28809801000357350355759419)
      ·
        refine ⟨43214701500536025533639129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28809801000357350355759419 43214701500536025533639129)
        ·
          refine ⟨32411026125402019150229347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43214701500536025533639129 32411026125402019150229347)
          ·
            refine ⟨48616539188103028725344021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32411026125402019150229347 48616539188103028725344021)
            ·
              refine ⟨2278900274442329471500501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48616539188103028725344021 2278900274442329471500501)
              ·
                refine ⟨53411725182242096988293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2278900274442329471500501 53411725182242096988293)
                ·
                  rfl

theorem cell21_702128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_702128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702128 prefixEnd_702128 := by exact prefixLift 702128
  have htrace : WordTrace (prefixWord ++ tailWord_702128) baseStart_702128 baseEnd_702128 := by
    simpa [prefixWord, tailWord_702128, baseEnd_702128] using wordTrace_append hprefix tailTrace_702128
  have hstable : (prefixWord ++ tailWord_702128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702128).length < 2 ^ (prefixWord ++ tailWord_702128).sum := by decide
  have hdescent : baseEnd_702128 < baseStart_702128 := by decide
  rcases family_descends (prefixWord ++ tailWord_702128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702162 : List Nat := [3, 2, 2, 2, 2, 3, 1, 6]
def baseStart_702162 : Nat := 118140960795 + 702162 * 2 ^ 59
def prefixEnd_702162 : Nat := 4983230072969 + 3 ^ 40 * 702162 * 2
def baseEnd_702162 : Nat := 53414311603316595799381

theorem tailTrace_702162 : CollatzResearch.WordTrace tailWord_702162 prefixEnd_702162 53414311603316595799381 := by
  unfold tailWord_702162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402488020548617141853185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17073301388129645711608493 6402488020548617141853185)
  ·
    refine ⟨4801866015411462856389889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6402488020548617141853185 4801866015411462856389889)
    ·
      refine ⟨3601399511558597142292417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4801866015411462856389889 3601399511558597142292417)
      ·
        refine ⟨2701049633668947856719313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3601399511558597142292417 2701049633668947856719313)
        ·
          refine ⟨2025787225251710892539485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2701049633668947856719313 2025787225251710892539485)
          ·
            refine ⟨759670209469391584702307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2025787225251710892539485 759670209469391584702307)
            ·
              refine ⟨1139505314204087377053461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759670209469391584702307 1139505314204087377053461)
              ·
                refine ⟨53414311603316595799381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1139505314204087377053461 53414311603316595799381)
                ·
                  rfl

theorem cell21_702162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_702162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702162 prefixEnd_702162 := by exact prefixLift 702162
  have htrace : WordTrace (prefixWord ++ tailWord_702162) baseStart_702162 baseEnd_702162 := by
    simpa [prefixWord, tailWord_702162, baseEnd_702162] using wordTrace_append hprefix tailTrace_702162
  have hstable : (prefixWord ++ tailWord_702162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702162).length < 2 ^ (prefixWord ++ tailWord_702162).sum := by decide
  have hdescent : baseEnd_702162 < baseStart_702162 := by decide
  rcases family_descends (prefixWord ++ tailWord_702162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702190 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_702190 : Nat := 118140960795 + 702190 * 2 ^ 59
def prefixEnd_702190 : Nat := 4983230072969 + 3 ^ 40 * 702190 * 2
def baseEnd_702190 : Nat := 160249324791427960931419

theorem tailTrace_702190 : CollatzResearch.WordTrace tailWord_702190 prefixEnd_702190 160249324791427960931419 := by
  unfold tailWord_702190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201371665761628668679003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17073982217395352899621349 3201371665761628668679003)
  ·
    refine ⟨4802057498642443003018505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3201371665761628668679003 4802057498642443003018505)
    ·
      refine ⟨3601543123981832252263879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4802057498642443003018505 3601543123981832252263879)
      ·
        refine ⟨5402314685972748378395819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3601543123981832252263879 5402314685972748378395819)
        ·
          refine ⟨8103472028959122567593729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402314685972748378395819 8103472028959122567593729)
          ·
            refine ⟨6077604021719341925695297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8103472028959122567593729 6077604021719341925695297)
            ·
              refine ⟨4558203016289506444271473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6077604021719341925695297 4558203016289506444271473)
              ·
                refine ⟨3418652262217129833203605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4558203016289506444271473 3418652262217129833203605)
                ·
                  refine ⟨160249324791427960931419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3418652262217129833203605 160249324791427960931419)
                  ·
                    rfl

theorem cell21_702190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_702190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702190 prefixEnd_702190 := by exact prefixLift 702190
  have htrace : WordTrace (prefixWord ++ tailWord_702190) baseStart_702190 baseEnd_702190 := by
    simpa [prefixWord, tailWord_702190, baseEnd_702190] using wordTrace_append hprefix tailTrace_702190
  have hstable : (prefixWord ++ tailWord_702190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702190).length < 2 ^ (prefixWord ++ tailWord_702190).sum := by decide
  have hdescent : baseEnd_702190 < baseStart_702190 := by decide
  rcases family_descends (prefixWord ++ tailWord_702190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702193 : List Nat := [1, 2, 2, 2, 2, 4, 2, 3, 3]
def baseStart_702193 : Nat := 118140960795 + 702193 * 2 ^ 59
def prefixEnd_702193 : Nat := 4983230072969 + 3 ^ 40 * 702193 * 2
def baseEnd_702193 : Nat := 160250009432300622381413

theorem tailTrace_702193 : CollatzResearch.WordTrace tailWord_702193 prefixEnd_702193 160250009432300622381413 := by
  unfold tailWord_702193
  simp only [CollatzResearch.WordTrace]
  refine ⟨25611082745082160861791233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17074055163388107241194155 25611082745082160861791233)
  ·
    refine ⟨19208312058811620646343425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25611082745082160861791233 19208312058811620646343425)
    ·
      refine ⟨14406234044108715484757569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19208312058811620646343425 14406234044108715484757569)
      ·
        refine ⟨10804675533081536613568177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14406234044108715484757569 10804675533081536613568177)
        ·
          refine ⟨8103506649811152460176133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10804675533081536613568177 8103506649811152460176133)
          ·
            refine ⟨1519407496839591086283025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8103506649811152460176133 1519407496839591086283025)
            ·
              refine ⟨1139555622629693314712269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1519407496839591086283025 1139555622629693314712269)
              ·
                refine ⟨427333358486134993017101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1139555622629693314712269 427333358486134993017101)
                ·
                  refine ⟨160250009432300622381413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427333358486134993017101 160250009432300622381413)
                  ·
                    rfl

theorem cell21_702193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_702193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702193 prefixEnd_702193 := by exact prefixLift 702193
  have htrace : WordTrace (prefixWord ++ tailWord_702193) baseStart_702193 baseEnd_702193 := by
    simpa [prefixWord, tailWord_702193, baseEnd_702193] using wordTrace_append hprefix tailTrace_702193
  have hstable : (prefixWord ++ tailWord_702193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702193).length < 2 ^ (prefixWord ++ tailWord_702193).sum := by decide
  have hdescent : baseEnd_702193 < baseStart_702193 := by decide
  rcases family_descends (prefixWord ++ tailWord_702193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702204 : List Nat := [2, 2, 2, 1, 3, 1, 10]
def baseStart_702204 : Nat := 118140960795 + 702204 * 2 ^ 59
def prefixEnd_702204 : Nat := 4983230072969 + 3 ^ 40 * 702204 * 2
def baseEnd_702204 : Nat := 17805835531351894188673

theorem tailTrace_702204 : CollatzResearch.WordTrace tailWord_702204 prefixEnd_702204 17805835531351894188673 := by
  unfold tailWord_702204
  simp only [CollatzResearch.WordTrace]
  refine ⟨12805741974021154870220833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17074322632028206493627777 12805741974021154870220833)
  ·
    refine ⟨9604306480515866152665625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12805741974021154870220833 9604306480515866152665625)
    ·
      refine ⟨7203229860386899614499219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9604306480515866152665625 7203229860386899614499219)
      ·
        refine ⟨10804844790580349421748829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7203229860386899614499219 10804844790580349421748829)
        ·
          refine ⟨4051816796467631033155811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10804844790580349421748829 4051816796467631033155811)
          ·
            refine ⟨6077725194701446549733717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051816796467631033155811 6077725194701446549733717)
            ·
              refine ⟨17805835531351894188673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6077725194701446549733717 17805835531351894188673)
              ·
                rfl

theorem cell21_702204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 10].length) (baseStart_702204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702204 prefixEnd_702204 := by exact prefixLift 702204
  have htrace : WordTrace (prefixWord ++ tailWord_702204) baseStart_702204 baseEnd_702204 := by
    simpa [prefixWord, tailWord_702204, baseEnd_702204] using wordTrace_append hprefix tailTrace_702204
  have hstable : (prefixWord ++ tailWord_702204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702204).length < 2 ^ (prefixWord ++ tailWord_702204).sum := by decide
  have hdescent : baseEnd_702204 < baseStart_702204 := by decide
  rcases family_descends (prefixWord ++ tailWord_702204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702266 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_702266 : Nat := 118140960795 + 702266 * 2 ^ 59
def prefixEnd_702266 : Nat := 4983230072969 + 3 ^ 40 * 702266 * 2
def baseEnd_702266 : Nat := 160266669026868717664597

theorem tailTrace_702266 : CollatzResearch.WordTrace tailWord_702266 prefixEnd_702266 160266669026868717664597 := by
  unfold tailWord_702266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403436318454423582299663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17075830182545129552799101 6403436318454423582299663)
  ·
    refine ⟨9605154477681635373449495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6403436318454423582299663 9605154477681635373449495)
    ·
      refine ⟨14407731716522453060174243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9605154477681635373449495 14407731716522453060174243)
      ·
        refine ⟨21611597574783679590261365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14407731716522453060174243 21611597574783679590261365)
        ·
          refine ⟨2026087272635969961587003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21611597574783679590261365 2026087272635969961587003)
          ·
            refine ⟨3039130908953954942380505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026087272635969961587003 3039130908953954942380505)
            ·
              refine ⟨2279348181715466206785379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039130908953954942380505 2279348181715466206785379)
              ·
                refine ⟨3419022272573199310178069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279348181715466206785379 3419022272573199310178069)
                ·
                  refine ⟨160266669026868717664597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3419022272573199310178069 160266669026868717664597)
                  ·
                    rfl

theorem cell21_702266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_702266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702266 prefixEnd_702266 := by exact prefixLift 702266
  have htrace : WordTrace (prefixWord ++ tailWord_702266) baseStart_702266 baseEnd_702266 := by
    simpa [prefixWord, tailWord_702266, baseEnd_702266] using wordTrace_append hprefix tailTrace_702266
  have hstable : (prefixWord ++ tailWord_702266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702266).length < 2 ^ (prefixWord ++ tailWord_702266).sum := by decide
  have hdescent : baseEnd_702266 < baseStart_702266 := by decide
  rcases family_descends (prefixWord ++ tailWord_702266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702269 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 5]
def baseStart_702269 : Nat := 118140960795 + 702269 * 2 ^ 59
def prefixEnd_702269 : Nat := 4983230072969 + 3 ^ 40 * 702269 * 2
def baseEnd_702269 : Nat := 160267353667741379114591

theorem tailTrace_702269 : CollatzResearch.WordTrace tailWord_702269 prefixEnd_702269 160267353667741379114591 := by
  unfold tailWord_702269
  simp only [CollatzResearch.WordTrace]
  refine ⟨25613854692806825841557861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17075903128537883894371907 25613854692806825841557861)
  ·
    refine ⟨4802597754901279845292099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25613854692806825841557861 4802597754901279845292099)
    ·
      refine ⟨7203896632351919767938149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802597754901279845292099 7203896632351919767938149)
      ·
        refine ⟨1350730618565984956488403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7203896632351919767938149 1350730618565984956488403)
        ·
          refine ⟨2026095927848977434732605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350730618565984956488403 2026095927848977434732605)
          ·
            refine ⟨759785972943366538024727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2026095927848977434732605 759785972943366538024727)
            ·
              refine ⟨1139678959415049807037091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759785972943366538024727 1139678959415049807037091)
              ·
                refine ⟨1709518439122574710555637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139678959415049807037091 1709518439122574710555637)
                ·
                  refine ⟨160267353667741379114591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1709518439122574710555637 160267353667741379114591)
                  ·
                    rfl

theorem cell21_702269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_702269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702269 prefixEnd_702269 := by exact prefixLift 702269
  have htrace : WordTrace (prefixWord ++ tailWord_702269) baseStart_702269 baseEnd_702269 := by
    simpa [prefixWord, tailWord_702269, baseEnd_702269] using wordTrace_append hprefix tailTrace_702269
  have hstable : (prefixWord ++ tailWord_702269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702269).length < 2 ^ (prefixWord ++ tailWord_702269).sum := by decide
  have hdescent : baseEnd_702269 < baseStart_702269 := by decide
  rcases family_descends (prefixWord ++ tailWord_702269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702280 : List Nat := [2, 1, 3, 1, 1, 4, 1, 8]
def baseStart_702280 : Nat := 118140960795 + 702280 * 2 ^ 59
def prefixEnd_702280 : Nat := 4983230072969 + 3 ^ 40 * 702280 * 2
def baseEnd_702280 : Nat := 53423288005869268143745

theorem tailTrace_702280 : CollatzResearch.WordTrace tailWord_702280 prefixEnd_702280 53423288005869268143745 := by
  unfold tailWord_702280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12807127947883487360104147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17076170597177983146805529 12807127947883487360104147)
  ·
    refine ⟨19210691921825231040156221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12807127947883487360104147 19210691921825231040156221)
    ·
      refine ⟨7204009470684461640058583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19210691921825231040156221 7204009470684461640058583)
      ·
        refine ⟨10806014206026692460087875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204009470684461640058583 10806014206026692460087875)
        ·
          refine ⟨16209021309040038690131813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10806014206026692460087875 16209021309040038690131813)
          ·
            refine ⟨3039191495445007254399715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16209021309040038690131813 3039191495445007254399715)
            ·
              refine ⟨4558787243167510881599573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3039191495445007254399715 4558787243167510881599573)
              ·
                refine ⟨53423288005869268143745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4558787243167510881599573 53423288005869268143745)
                ·
                  rfl

theorem cell21_702280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_702280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702280 prefixEnd_702280 := by exact prefixLift 702280
  have htrace : WordTrace (prefixWord ++ tailWord_702280) baseStart_702280 baseEnd_702280 := by
    simpa [prefixWord, tailWord_702280, baseEnd_702280] using wordTrace_append hprefix tailTrace_702280
  have hstable : (prefixWord ++ tailWord_702280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702280).length < 2 ^ (prefixWord ++ tailWord_702280).sum := by decide
  have hdescent : baseEnd_702280 < baseStart_702280 := by decide
  rcases family_descends (prefixWord ++ tailWord_702280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702314 : List Nat := [3, 1, 3, 4, 2, 8]
def baseStart_702314 : Nat := 118140960795 + 702314 * 2 ^ 59
def prefixEnd_702314 : Nat := 4983230072969 + 3 ^ 40 * 702314 * 2
def baseEnd_702314 : Nat := 5936208269660418550537

theorem tailTrace_702314 : CollatzResearch.WordTrace tailWord_702314 prefixEnd_702314 5936208269660418550537 := by
  unfold tailWord_702314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403873994410949631736499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17076997318429199017963997 6403873994410949631736499)
  ·
    refine ⟨9605810991616424447604749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6403873994410949631736499 9605810991616424447604749)
    ·
      refine ⟨3602179121856159167851781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9605810991616424447604749 3602179121856159167851781)
      ·
        refine ⟨675408585348029843972209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3602179121856159167851781 675408585348029843972209)
        ·
          refine ⟨506556439011022382979157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675408585348029843972209 506556439011022382979157)
          ·
            refine ⟨5936208269660418550537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 506556439011022382979157 5936208269660418550537)
            ·
              rfl

theorem cell21_702314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 8].length) (baseStart_702314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702314 prefixEnd_702314 := by exact prefixLift 702314
  have htrace : WordTrace (prefixWord ++ tailWord_702314) baseStart_702314 baseEnd_702314 := by
    simpa [prefixWord, tailWord_702314, baseEnd_702314] using wordTrace_append hprefix tailTrace_702314
  have hstable : (prefixWord ++ tailWord_702314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702314).length < 2 ^ (prefixWord ++ tailWord_702314).sum := by decide
  have hdescent : baseEnd_702314 < baseStart_702314 := by decide
  rcases family_descends (prefixWord ++ tailWord_702314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702376 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_702376 : Nat := 118140960795 + 702376 * 2 ^ 59
def prefixEnd_702376 : Nat := 4983230072969 + 3 ^ 40 * 702376 * 2
def baseEnd_702376 : Nat := 160291772525532970831039

theorem tailTrace_702376 : CollatzResearch.WordTrace tailWord_702376 prefixEnd_702376 160291772525532970831039 := by
  unfold tailWord_702376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12808878651709591557851491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17078504868946122077135321 12808878651709591557851491)
  ·
    refine ⟨19213317977564387336777237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12808878651709591557851491 19213317977564387336777237)
    ·
      refine ⟨900624280198330656411433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19213317977564387336777237 900624280198330656411433)
      ·
        refine ⟨675468210148747992308575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 900624280198330656411433 675468210148747992308575)
        ·
          refine ⟨1013202315223121988462863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675468210148747992308575 1013202315223121988462863)
          ·
            refine ⟨1519803472834682982694295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013202315223121988462863 1519803472834682982694295)
            ·
              refine ⟨2279705209252024474041443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519803472834682982694295 2279705209252024474041443)
              ·
                refine ⟨3419557813878036711062165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279705209252024474041443 3419557813878036711062165)
                ·
                  refine ⟨160291772525532970831039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3419557813878036711062165 160291772525532970831039)
                  ·
                    rfl

theorem cell21_702376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_702376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702376 prefixEnd_702376 := by exact prefixLift 702376
  have htrace : WordTrace (prefixWord ++ tailWord_702376) baseStart_702376 baseEnd_702376 := by
    simpa [prefixWord, tailWord_702376, baseEnd_702376] using wordTrace_append hprefix tailTrace_702376
  have hstable : (prefixWord ++ tailWord_702376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702376).length < 2 ^ (prefixWord ++ tailWord_702376).sum := by decide
  have hdescent : baseEnd_702376 < baseStart_702376 := by decide
  rcases family_descends (prefixWord ++ tailWord_702376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702387 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 5]
def baseStart_702387 : Nat := 118140960795 + 702387 * 2 ^ 59
def prefixEnd_702387 : Nat := 4983230072969 + 3 ^ 40 * 702387 * 2
def baseEnd_702387 : Nat := 160294282875399396147683

theorem tailTrace_702387 : CollatzResearch.WordTrace tailWord_702387 prefixEnd_702387 160294282875399396147683 := by
  unfold tailWord_702387
  simp only [CollatzResearch.WordTrace]
  refine ⟨25618158506379331994353415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17078772337586221329568943 25618158506379331994353415)
  ·
    refine ⟨38427237759568997991530123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25618158506379331994353415 38427237759568997991530123)
    ·
      refine ⟨57640856639353496987295185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38427237759568997991530123 57640856639353496987295185)
      ·
        refine ⟨43230642479515122740471389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57640856639353496987295185 43230642479515122740471389)
        ·
          refine ⟨16211490929818171027676771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43230642479515122740471389 16211490929818171027676771)
          ·
            refine ⟨24317236394727256541515157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16211490929818171027676771 24317236394727256541515157)
            ·
              refine ⟨1139870456002840150383523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24317236394727256541515157 1139870456002840150383523)
              ·
                refine ⟨1709805684004260225575285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139870456002840150383523 1709805684004260225575285)
                ·
                  refine ⟨160294282875399396147683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1709805684004260225575285 160294282875399396147683)
                  ·
                    rfl

theorem cell21_702387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_702387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702387 prefixEnd_702387 := by exact prefixLift 702387
  have htrace : WordTrace (prefixWord ++ tailWord_702387) baseStart_702387 baseEnd_702387 := by
    simpa [prefixWord, tailWord_702387, baseEnd_702387] using wordTrace_append hprefix tailTrace_702387
  have hstable : (prefixWord ++ tailWord_702387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702387).length < 2 ^ (prefixWord ++ tailWord_702387).sum := by decide
  have hdescent : baseEnd_702387 < baseStart_702387 := by decide
  rcases family_descends (prefixWord ++ tailWord_702387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702421 : List Nat := [1, 3, 2, 3, 2, 1, 3, 3, 3]
def baseStart_702421 : Nat := 118140960795 + 702421 * 2 ^ 59
def prefixEnd_702421 : Nat := 4983230072969 + 3 ^ 40 * 702421 * 2
def baseEnd_702421 : Nat := 160302042138622892580947

theorem tailTrace_702421 : CollatzResearch.WordTrace tailWord_702421 prefixEnd_702421 160302042138622892580947 := by
  unfold tailWord_702421
  simp only [CollatzResearch.WordTrace]
  refine ⟨25619398588256155801091117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17079599058837437200727411 25619398588256155801091117)
  ·
    refine ⟨9607274470596058425409169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25619398588256155801091117 9607274470596058425409169)
    ·
      refine ⟨7205455852947043819056877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9607274470596058425409169 7205455852947043819056877)
      ·
        refine ⟨2702045944855141432146329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7205455852947043819056877 2702045944855141432146329)
        ·
          refine ⟨2026534458641356074109747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2702045944855141432146329 2026534458641356074109747)
          ·
            refine ⟨3039801687962034111164621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026534458641356074109747 3039801687962034111164621)
            ·
              refine ⟨1139925632985762791686733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3039801687962034111164621 1139925632985762791686733)
              ·
                refine ⟨427472112369661046882525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1139925632985762791686733 427472112369661046882525)
                ·
                  refine ⟨160302042138622892580947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427472112369661046882525 160302042138622892580947)
                  ·
                    rfl

theorem cell21_702421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_702421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702421 prefixEnd_702421 := by exact prefixLift 702421
  have htrace : WordTrace (prefixWord ++ tailWord_702421) baseStart_702421 baseEnd_702421 := by
    simpa [prefixWord, tailWord_702421, baseEnd_702421] using wordTrace_append hprefix tailTrace_702421
  have hstable : (prefixWord ++ tailWord_702421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702421).length < 2 ^ (prefixWord ++ tailWord_702421).sum := by decide
  have hdescent : baseEnd_702421 < baseStart_702421 := by decide
  rcases family_descends (prefixWord ++ tailWord_702421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702449 : List Nat := [1, 2, 2, 2, 5, 1, 2, 6]
def baseStart_702449 : Nat := 118140960795 + 702449 * 2 ^ 59
def prefixEnd_702449 : Nat := 4983230072969 + 3 ^ 40 * 702449 * 2
def baseEnd_702449 : Nat := 53436144040033688704741

theorem tailTrace_702449 : CollatzResearch.WordTrace tailWord_702449 prefixEnd_702449 53436144040033688704741 := by
  unfold tailWord_702449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25620419832154716583110401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17080279888103144388740267 25620419832154716583110401)
  ·
    refine ⟨19215314874116037437332801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25620419832154716583110401 19215314874116037437332801)
    ·
      refine ⟨14411486155587028077999601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19215314874116037437332801 14411486155587028077999601)
      ·
        refine ⟨10808614616690271058499701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14411486155587028077999601 10808614616690271058499701)
        ·
          refine ⟨1013307620314712911734347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10808614616690271058499701 1013307620314712911734347)
          ·
            refine ⟨1519961430472069367601521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013307620314712911734347 1519961430472069367601521)
            ·
              refine ⟨1139971072854052025701141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1519961430472069367601521 1139971072854052025701141)
              ·
                refine ⟨53436144040033688704741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1139971072854052025701141 53436144040033688704741)
                ·
                  rfl

theorem cell21_702449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 6].length) (baseStart_702449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702449 prefixEnd_702449 := by exact prefixLift 702449
  have htrace : WordTrace (prefixWord ++ tailWord_702449) baseStart_702449 baseEnd_702449 := by
    simpa [prefixWord, tailWord_702449, baseEnd_702449] using wordTrace_append hprefix tailTrace_702449
  have hstable : (prefixWord ++ tailWord_702449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702449).length < 2 ^ (prefixWord ++ tailWord_702449).sum := by decide
  have hdescent : baseEnd_702449 < baseStart_702449 := by decide
  rcases family_descends (prefixWord ++ tailWord_702449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702497 : List Nat := [1, 2, 3, 2, 4, 1, 1, 4, 3]
def baseStart_702497 : Nat := 118140960795 + 702497 * 2 ^ 59
def prefixEnd_702497 : Nat := 4983230072969 + 3 ^ 40 * 702497 * 2
def baseEnd_702497 : Nat := 160319386374063649314125

theorem tailTrace_702497 : CollatzResearch.WordTrace tailWord_702497 prefixEnd_702497 160319386374063649314125 := by
  unfold tailWord_702497
  simp only [CollatzResearch.WordTrace]
  refine ⟨25622170535980820780857745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17081447023987213853905163 25622170535980820780857745)
  ·
    refine ⟨19216627901985615585643309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25622170535980820780857745 19216627901985615585643309)
    ·
      refine ⟨7206235463244605844616241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19216627901985615585643309 7206235463244605844616241)
      ·
        refine ⟨5404676597433454383462181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7206235463244605844616241 5404676597433454383462181)
        ·
          refine ⟨1013376862018772696899159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5404676597433454383462181 1013376862018772696899159)
          ·
            refine ⟨1520065293028159045348739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013376862018772696899159 1520065293028159045348739)
            ·
              refine ⟨2280097939542238568023109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520065293028159045348739 2280097939542238568023109)
              ·
                refine ⟨427518363664169731504333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2280097939542238568023109 427518363664169731504333)
                ·
                  refine ⟨160319386374063649314125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427518363664169731504333 160319386374063649314125)
                  ·
                    rfl

theorem cell21_702497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_702497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702497 prefixEnd_702497 := by exact prefixLift 702497
  have htrace : WordTrace (prefixWord ++ tailWord_702497) baseStart_702497 baseEnd_702497 := by
    simpa [prefixWord, tailWord_702497, baseEnd_702497] using wordTrace_append hprefix tailTrace_702497
  have hstable : (prefixWord ++ tailWord_702497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702497).length < 2 ^ (prefixWord ++ tailWord_702497).sum := by decide
  have hdescent : baseEnd_702497 < baseStart_702497 := by decide
  rcases family_descends (prefixWord ++ tailWord_702497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702525 : List Nat := [1, 4, 1, 3, 1, 1, 5, 5]
def baseStart_702525 : Nat := 118140960795 + 702525 * 2 ^ 59
def prefixEnd_702525 : Nat := 4983230072969 + 3 ^ 40 * 702525 * 2
def baseEnd_702525 : Nat := 53441925451847274282467

theorem tailTrace_702525 : CollatzResearch.WordTrace tailWord_702525 prefixEnd_702525 53441925451847274282467 := by
  unfold tailWord_702525
  simp only [CollatzResearch.WordTrace]
  refine ⟨25623191779879381562877029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17082127853252921041918019 25623191779879381562877029)
  ·
    refine ⟨4804348458727384043039443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25623191779879381562877029 4804348458727384043039443)
    ·
      refine ⟨7206522688091076064559165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804348458727384043039443 7206522688091076064559165)
      ·
        refine ⟨2702446008034153524209687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7206522688091076064559165 2702446008034153524209687)
        ·
          refine ⟨4053669012051230286314531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702446008034153524209687 4053669012051230286314531)
          ·
            refine ⟨6080503518076845429471797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053669012051230286314531 6080503518076845429471797)
            ·
              refine ⟨570047204819704259012981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6080503518076845429471797 570047204819704259012981)
              ·
                refine ⟨53441925451847274282467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 570047204819704259012981 53441925451847274282467)
                ·
                  rfl

theorem cell21_702525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 5].length) (baseStart_702525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702525 prefixEnd_702525 := by exact prefixLift 702525
  have htrace : WordTrace (prefixWord ++ tailWord_702525) baseStart_702525 baseEnd_702525 := by
    simpa [prefixWord, tailWord_702525, baseEnd_702525] using wordTrace_append hprefix tailTrace_702525
  have hstable : (prefixWord ++ tailWord_702525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702525).length < 2 ^ (prefixWord ++ tailWord_702525).sum := by decide
  have hdescent : baseEnd_702525 < baseStart_702525 := by decide
  rcases family_descends (prefixWord ++ tailWord_702525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702553 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 6]
def baseStart_702553 : Nat := 118140960795 + 702553 * 2 ^ 59
def prefixEnd_702553 : Nat := 4983230072969 + 3 ^ 40 * 702553 * 2
def baseEnd_702553 : Nat := 160332166337019996380677

theorem tailTrace_702553 : CollatzResearch.WordTrace tailWord_702553 prefixEnd_702553 160332166337019996380677 := by
  unfold tailWord_702553
  simp only [CollatzResearch.WordTrace]
  refine ⟨25624213023777942344896313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17082808682518628229930875 25624213023777942344896313)
  ·
    refine ⟨19218159767833456758672235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25624213023777942344896313 19218159767833456758672235)
    ·
      refine ⟨28827239651750185138008353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19218159767833456758672235 28827239651750185138008353)
      ·
        refine ⟨21620429738812638853506265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28827239651750185138008353 21620429738812638853506265)
        ·
          refine ⟨16215322304109479140129699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21620429738812638853506265 16215322304109479140129699)
          ·
            refine ⟨24322983456164218710194549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16215322304109479140129699 24322983456164218710194549)
            ·
              refine ⟨2280279699015395504080739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24322983456164218710194549 2280279699015395504080739)
              ·
                refine ⟨3420419548523093256121109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280279699015395504080739 3420419548523093256121109)
                ·
                  refine ⟨160332166337019996380677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3420419548523093256121109 160332166337019996380677)
                  ·
                    rfl

theorem cell21_702553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_702553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702553 prefixEnd_702553 := by exact prefixLift 702553
  have htrace : WordTrace (prefixWord ++ tailWord_702553) baseStart_702553 baseEnd_702553 := by
    simpa [prefixWord, tailWord_702553, baseEnd_702553] using wordTrace_append hprefix tailTrace_702553
  have hstable : (prefixWord ++ tailWord_702553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702553).length < 2 ^ (prefixWord ++ tailWord_702553).sum := by decide
  have hdescent : baseEnd_702553 < baseStart_702553 := by decide
  rcases family_descends (prefixWord ++ tailWord_702553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702556 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_702556 : Nat := 118140960795 + 702556 * 2 ^ 59
def prefixEnd_702556 : Nat := 4983230072969 + 3 ^ 40 * 702556 * 2
def baseEnd_702556 : Nat := 160332850977892657830671

theorem tailTrace_702556 : CollatzResearch.WordTrace tailWord_702556 prefixEnd_702556 160332850977892657830671 := by
  unfold tailWord_702556
  simp only [CollatzResearch.WordTrace]
  refine ⟨12812161221383536928627761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17082881628511382571503681 12812161221383536928627761)
  ·
    refine ⟨9609120916037652696470821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12812161221383536928627761 9609120916037652696470821)
    ·
      refine ⟨1801710171757059880588279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9609120916037652696470821 1801710171757059880588279)
      ·
        refine ⟨2702565257635589820882419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801710171757059880588279 2702565257635589820882419)
        ·
          refine ⟨4053847886453384731323629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702565257635589820882419 4053847886453384731323629)
          ·
            refine ⟨1520192957420019274246361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4053847886453384731323629 1520192957420019274246361)
            ·
              refine ⟨1140144718065014455684771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520192957420019274246361 1140144718065014455684771)
              ·
                refine ⟨1710217077097521683527157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140144718065014455684771 1710217077097521683527157)
                ·
                  refine ⟨160332850977892657830671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1710217077097521683527157 160332850977892657830671)
                  ·
                    rfl

theorem cell21_702556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_702556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702556 prefixEnd_702556 := by exact prefixLift 702556
  have htrace : WordTrace (prefixWord ++ tailWord_702556) baseStart_702556 baseEnd_702556 := by
    simpa [prefixWord, tailWord_702556, baseEnd_702556] using wordTrace_append hprefix tailTrace_702556
  have hstable : (prefixWord ++ tailWord_702556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702556).length < 2 ^ (prefixWord ++ tailWord_702556).sum := by decide
  have hdescent : baseEnd_702556 < baseStart_702556 := by decide
  rcases family_descends (prefixWord ++ tailWord_702556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702660 : List Nat := [2, 3, 3, 1, 2, 10]
def baseStart_702660 : Nat := 118140960795 + 702660 * 2 ^ 59
def prefixEnd_702660 : Nat := 4983230072969 + 3 ^ 40 * 702660 * 2
def baseEnd_702660 : Nat := 5939132784993021781375

theorem tailTrace_702660 : CollatzResearch.WordTrace tailWord_702660 prefixEnd_702660 5939132784993021781375 := by
  unfold tailWord_702660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12814057817195149809520717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17085410422926866412694289 12814057817195149809520717)
  ·
    refine ⟨4805271681448181178570269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12814057817195149809520717 4805271681448181178570269)
    ·
      refine ⟨1801976880543067941963851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4805271681448181178570269 1801976880543067941963851)
      ·
        refine ⟨2702965320814601912945777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801976880543067941963851 2702965320814601912945777)
        ·
          refine ⟨2027223990610951434709333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2702965320814601912945777 2027223990610951434709333)
          ·
            refine ⟨5939132784993021781375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2027223990610951434709333 5939132784993021781375)
            ·
              rfl

theorem cell21_702660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 10].length) (baseStart_702660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702660 prefixEnd_702660 := by exact prefixLift 702660
  have htrace : WordTrace (prefixWord ++ tailWord_702660) baseStart_702660 baseEnd_702660 := by
    simpa [prefixWord, tailWord_702660, baseEnd_702660] using wordTrace_append hprefix tailTrace_702660
  have hstable : (prefixWord ++ tailWord_702660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702660).length < 2 ^ (prefixWord ++ tailWord_702660).sum := by decide
  have hdescent : baseEnd_702660 < baseStart_702660 := by decide
  rcases family_descends (prefixWord ++ tailWord_702660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702719 : List Nat := [1, 1, 2, 2, 1, 4, 10]
def baseStart_702719 : Nat := 118140960795 + 702719 * 2 ^ 59
def prefixEnd_702719 : Nat := 4983230072969 + 3 ^ 40 * 702719 * 2
def baseEnd_702719 : Nat := 17818894422071177401519

theorem tailTrace_702719 : CollatzResearch.WordTrace tailWord_702719 prefixEnd_702719 17818894422071177401519 := by
  unfold tailWord_702719
  simp only [CollatzResearch.WordTrace]
  refine ⟨25630267541176552695439211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17086845027451035130292807 25630267541176552695439211)
  ·
    refine ⟨38445401311764829043158817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25630267541176552695439211 38445401311764829043158817)
    ·
      refine ⟨28834050983823621782369113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38445401311764829043158817 28834050983823621782369113)
      ·
        refine ⟨21625538237867716336776835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28834050983823621782369113 21625538237867716336776835)
        ·
          refine ⟨32438307356801574505165253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21625538237867716336776835 32438307356801574505165253)
          ·
            refine ⟨6082182629400295219718485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32438307356801574505165253 6082182629400295219718485)
            ·
              refine ⟨17818894422071177401519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6082182629400295219718485 17818894422071177401519)
              ·
                rfl

theorem cell21_702719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 10].length) (baseStart_702719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702719 prefixEnd_702719 := by exact prefixLift 702719
  have htrace : WordTrace (prefixWord ++ tailWord_702719) baseStart_702719 baseEnd_702719 := by
    simpa [prefixWord, tailWord_702719, baseEnd_702719] using wordTrace_append hprefix tailTrace_702719
  have hstable : (prefixWord ++ tailWord_702719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702719).length < 2 ^ (prefixWord ++ tailWord_702719).sum := by decide
  have hdescent : baseEnd_702719 < baseStart_702719 := by decide
  rcases family_descends (prefixWord ++ tailWord_702719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702871 : List Nat := [1, 1, 3, 3, 1, 1, 2, 9]
def baseStart_702871 : Nat := 118140960795 + 702871 * 2 ^ 59
def prefixEnd_702871 : Nat := 4983230072969 + 3 ^ 40 * 702871 * 2
def baseEnd_702871 : Nat := 53468246089840703360009

theorem tailTrace_702871 : CollatzResearch.WordTrace tailWord_702871 prefixEnd_702871 53468246089840703360009 := by
  unfold tailWord_702871
  simp only [CollatzResearch.WordTrace]
  refine ⟨25635811436625882654972467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17090540957750588436648311 25635811436625882654972467)
  ·
    refine ⟨38453717154938823982458701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25635811436625882654972467 38453717154938823982458701)
    ·
      refine ⟨14420143933102058993422013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38453717154938823982458701 14420143933102058993422013)
      ·
        refine ⟨5407553974913272122533255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14420143933102058993422013 5407553974913272122533255)
        ·
          refine ⟨8111330962369908183799883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407553974913272122533255 8111330962369908183799883)
          ·
            refine ⟨12166996443554862275699825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8111330962369908183799883 12166996443554862275699825)
            ·
              refine ⟨9125247332666146706774869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12166996443554862275699825 9125247332666146706774869)
              ·
                refine ⟨53468246089840703360009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9125247332666146706774869 53468246089840703360009)
                ·
                  rfl

theorem cell21_702871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 9].length) (baseStart_702871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702871 prefixEnd_702871 := by exact prefixLift 702871
  have htrace : WordTrace (prefixWord ++ tailWord_702871) baseStart_702871 baseEnd_702871 := by
    simpa [prefixWord, tailWord_702871, baseEnd_702871] using wordTrace_append hprefix tailTrace_702871
  have hstable : (prefixWord ++ tailWord_702871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702871).length < 2 ^ (prefixWord ++ tailWord_702871).sum := by decide
  have hdescent : baseEnd_702871 < baseStart_702871 := by decide
  rcases family_descends (prefixWord ++ tailWord_702871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702877 : List Nat := [1, 4, 2, 1, 4, 1, 2, 3, 3]
def baseStart_702877 : Nat := 118140960795 + 702877 * 2 ^ 59
def prefixEnd_702877 : Nat := 4983230072969 + 3 ^ 40 * 702877 * 2
def baseEnd_702877 : Nat := 160406107551267432980015

theorem tailTrace_702877 : CollatzResearch.WordTrace tailWord_702877 prefixEnd_702877 160406107551267432980015 := by
  unfold tailWord_702877
  simp only [CollatzResearch.WordTrace]
  refine ⟨25636030274604145679690885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17090686849736097119793923 25636030274604145679690885)
  ·
    refine ⟨4806755676488277314942041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25636030274604145679690885 4806755676488277314942041)
    ·
      refine ⟨3605066757366207986206531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4806755676488277314942041 3605066757366207986206531)
      ·
        refine ⟨5407600136049311979309797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605066757366207986206531 5407600136049311979309797)
        ·
          refine ⟨1013925025509245996120587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5407600136049311979309797 1013925025509245996120587)
          ·
            refine ⟨1520887538263868994180881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013925025509245996120587 1520887538263868994180881)
            ·
              refine ⟨1140665653697901745635661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520887538263868994180881 1140665653697901745635661)
              ·
                refine ⟨427749620136713154613373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1140665653697901745635661 427749620136713154613373)
                ·
                  refine ⟨160406107551267432980015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427749620136713154613373 160406107551267432980015)
                  ·
                    rfl

theorem cell21_702877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_702877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702877 prefixEnd_702877 := by exact prefixLift 702877
  have htrace : WordTrace (prefixWord ++ tailWord_702877) baseStart_702877 baseEnd_702877 := by
    simpa [prefixWord, tailWord_702877, baseEnd_702877] using wordTrace_append hprefix tailTrace_702877
  have hstable : (prefixWord ++ tailWord_702877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702877).length < 2 ^ (prefixWord ++ tailWord_702877).sum := by decide
  have hdescent : baseEnd_702877 < baseStart_702877 := by decide
  rcases family_descends (prefixWord ++ tailWord_702877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702933 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 6]
def baseStart_702933 : Nat := 118140960795 + 702933 * 2 ^ 59
def prefixEnd_702933 : Nat := 4983230072969 + 3 ^ 40 * 702933 * 2
def baseEnd_702933 : Nat := 160418887514223780046567

theorem tailTrace_702933 : CollatzResearch.WordTrace tailWord_702933 prefixEnd_702933 160418887514223780046567 := by
  unfold tailWord_702933
  simp only [CollatzResearch.WordTrace]
  refine ⟨25638072762401267243729453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17092048508267511495819635 25638072762401267243729453)
  ·
    refine ⟨9614277285900475216398545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25638072762401267243729453 9614277285900475216398545)
    ·
      refine ⟨7210707964425356412298909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9614277285900475216398545 7210707964425356412298909)
      ·
        refine ⟨2704015486659508654612091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7210707964425356412298909 2704015486659508654612091)
        ·
          refine ⟨4056023229989262981918137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704015486659508654612091 4056023229989262981918137)
          ·
            refine ⟨3042017422491947236438603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4056023229989262981918137 3042017422491947236438603)
            ·
              refine ⟨4563026133737920854657905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042017422491947236438603 4563026133737920854657905)
              ·
                refine ⟨3422269600303440640993429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4563026133737920854657905 3422269600303440640993429)
                ·
                  refine ⟨160418887514223780046567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3422269600303440640993429 160418887514223780046567)
                  ·
                    rfl

theorem cell21_702933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_702933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702933 prefixEnd_702933 := by exact prefixLift 702933
  have htrace : WordTrace (prefixWord ++ tailWord_702933) baseStart_702933 baseEnd_702933 := by
    simpa [prefixWord, tailWord_702933, baseEnd_702933] using wordTrace_append hprefix tailTrace_702933
  have hstable : (prefixWord ++ tailWord_702933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702933).length < 2 ^ (prefixWord ++ tailWord_702933).sum := by decide
  have hdescent : baseEnd_702933 < baseStart_702933 := by decide
  rcases family_descends (prefixWord ++ tailWord_702933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_702995 : List Nat := [1, 1, 1, 2, 1, 5, 2, 5, 3]
def baseStart_702995 : Nat := 118140960795 + 702995 * 2 ^ 59
def prefixEnd_702995 : Nat := 4983230072969 + 3 ^ 40 * 702995 * 2
def baseEnd_702995 : Nat := 160433036758925450013107

theorem tailTrace_702995 : CollatzResearch.WordTrace tailWord_702995 prefixEnd_702995 160433036758925450013107 := by
  unfold tailWord_702995
  simp only [CollatzResearch.WordTrace]
  refine ⟨25640334088176651832486439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17093556058784434554990959 25640334088176651832486439)
  ·
    refine ⟨38460501132264977748729659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25640334088176651832486439 38460501132264977748729659)
    ·
      refine ⟨57690751698397466623094489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38460501132264977748729659 57690751698397466623094489)
      ·
        refine ⟨43268063773798099967320867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57690751698397466623094489 43268063773798099967320867)
        ·
          refine ⟨64902095660697149950981301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43268063773798099967320867 64902095660697149950981301)
          ·
            refine ⟨6084571468190357807904497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64902095660697149950981301 6084571468190357807904497)
            ·
              refine ⟨4563428601142768355928373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6084571468190357807904497 4563428601142768355928373)
              ·
                refine ⟨427821431357134533368285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4563428601142768355928373 427821431357134533368285)
                ·
                  refine ⟨160433036758925450013107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427821431357134533368285 160433036758925450013107)
                  ·
                    rfl

theorem cell21_702995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 3].length) (baseStart_702995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_702995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_702995 prefixEnd_702995 := by exact prefixLift 702995
  have htrace : WordTrace (prefixWord ++ tailWord_702995) baseStart_702995 baseEnd_702995 := by
    simpa [prefixWord, tailWord_702995, baseEnd_702995] using wordTrace_append hprefix tailTrace_702995
  have hstable : (prefixWord ++ tailWord_702995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_702995).length < 2 ^ (prefixWord ++ tailWord_702995).sum := by decide
  have hdescent : baseEnd_702995 < baseStart_702995 := by decide
  rcases family_descends (prefixWord ++ tailWord_702995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703015 : List Nat := [1, 1, 7, 2, 2, 1, 1, 6]
def baseStart_703015 : Nat := 118140960795 + 703015 * 2 ^ 59
def prefixEnd_703015 : Nat := 4983230072969 + 3 ^ 40 * 703015 * 2
def baseEnd_703015 : Nat := 53479200343803286559911

theorem tailTrace_703015 : CollatzResearch.WordTrace tailWord_703015 prefixEnd_703015 53479200343803286559911 := by
  unfold tailWord_703015
  simp only [CollatzResearch.WordTrace]
  refine ⟨25641063548104195248214499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17094042365402796832142999 25641063548104195248214499)
  ·
    refine ⟨38461595322156292872321749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25641063548104195248214499 38461595322156292872321749)
    ·
      refine ⟨901443640363038114195041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 38461595322156292872321749 901443640363038114195041)
      ·
        refine ⟨676082730272278585646281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 901443640363038114195041 676082730272278585646281)
        ·
          refine ⟨507062047704208939234711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676082730272278585646281 507062047704208939234711)
          ·
            refine ⟨760593071556313408852067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507062047704208939234711 760593071556313408852067)
            ·
              refine ⟨1140889607334470113278101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760593071556313408852067 1140889607334470113278101)
              ·
                refine ⟨53479200343803286559911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1140889607334470113278101 53479200343803286559911)
                ·
                  rfl

theorem cell21_703015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 6].length) (baseStart_703015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703015 prefixEnd_703015 := by exact prefixLift 703015
  have htrace : WordTrace (prefixWord ++ tailWord_703015) baseStart_703015 baseEnd_703015 := by
    simpa [prefixWord, tailWord_703015, baseEnd_703015] using wordTrace_append hprefix tailTrace_703015
  have hstable : (prefixWord ++ tailWord_703015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703015).length < 2 ^ (prefixWord ++ tailWord_703015).sum := by decide
  have hdescent : baseEnd_703015 < baseStart_703015 := by decide
  rcases family_descends (prefixWord ++ tailWord_703015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703046 : List Nat := [6, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_703046 : Nat := 118140960795 + 703046 * 2 ^ 59
def prefixEnd_703046 : Nat := 4983230072969 + 3 ^ 40 * 703046 * 2
def baseEnd_703046 : Nat := 160444675653760694663003

theorem tailTrace_703046 : CollatzResearch.WordTrace tailWord_703046 prefixEnd_703046 160444675653760694663003 := by
  unfold tailWord_703046
  simp only [CollatzResearch.WordTrace]
  refine ⟨801318569093496485706031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17094796140661258361728661 801318569093496485706031)
  ·
    refine ⟨1201977853640244728559047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 801318569093496485706031 1201977853640244728559047)
    ·
      refine ⟨1802966780460367092838571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1201977853640244728559047 1802966780460367092838571)
      ·
        refine ⟨2704450170690550639257857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802966780460367092838571 2704450170690550639257857)
        ·
          refine ⟨2028337628017912979443393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2704450170690550639257857 2028337628017912979443393)
          ·
            refine ⟨1521253221013434734582545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2028337628017912979443393 1521253221013434734582545)
            ·
              refine ⟨1140939915760076050936909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521253221013434734582545 1140939915760076050936909)
              ·
                refine ⟨427852468410028519101341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1140939915760076050936909 427852468410028519101341)
                ·
                  refine ⟨160444675653760694663003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427852468410028519101341 160444675653760694663003)
                  ·
                    rfl

theorem cell21_703046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_703046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703046 prefixEnd_703046 := by exact prefixLift 703046
  have htrace : WordTrace (prefixWord ++ tailWord_703046) baseStart_703046 baseEnd_703046 := by
    simpa [prefixWord, tailWord_703046, baseEnd_703046] using wordTrace_append hprefix tailTrace_703046
  have hstable : (prefixWord ++ tailWord_703046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703046).length < 2 ^ (prefixWord ++ tailWord_703046).sum := by decide
  have hdescent : baseEnd_703046 < baseStart_703046 := by decide
  rcases family_descends (prefixWord ++ tailWord_703046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703136 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 4]
def baseStart_703136 : Nat := 118140960795 + 703136 * 2 ^ 59
def prefixEnd_703136 : Nat := 4983230072969 + 3 ^ 40 * 703136 * 2
def baseEnd_703136 : Nat := 160465214879940538162819

theorem tailTrace_703136 : CollatzResearch.WordTrace tailWord_703136 prefixEnd_703136 160465214879940538162819 := by
  unfold tailWord_703136
  simp only [CollatzResearch.WordTrace]
  refine ⟨12822738390332916456684631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17096984520443888608912841 12822738390332916456684631)
  ·
    refine ⟨19234107585499374685026947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12822738390332916456684631 19234107585499374685026947)
    ·
      refine ⟨28851161378249062027540421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19234107585499374685026947 28851161378249062027540421)
      ·
        refine ⟨5409592758421699130163829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28851161378249062027540421 5409592758421699130163829)
        ·
          refine ⟨507149321102034293452859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5409592758421699130163829 507149321102034293452859)
          ·
            refine ⟨760723981653051440179289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507149321102034293452859 760723981653051440179289)
            ·
              refine ⟨570542986239788580134467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760723981653051440179289 570542986239788580134467)
              ·
                refine ⟨855814479359682870201701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570542986239788580134467 855814479359682870201701)
                ·
                  refine ⟨160465214879940538162819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 855814479359682870201701 160465214879940538162819)
                  ·
                    rfl

theorem cell21_703136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_703136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703136 prefixEnd_703136 := by exact prefixLift 703136
  have htrace : WordTrace (prefixWord ++ tailWord_703136) baseStart_703136 baseEnd_703136 := by
    simpa [prefixWord, tailWord_703136, baseEnd_703136] using wordTrace_append hprefix tailTrace_703136
  have hstable : (prefixWord ++ tailWord_703136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703136).length < 2 ^ (prefixWord ++ tailWord_703136).sum := by decide
  have hdescent : baseEnd_703136 < baseStart_703136 := by decide
  rcases family_descends (prefixWord ++ tailWord_703136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703178 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_703178 : Nat := 118140960795 + 703178 * 2 ^ 59
def prefixEnd_703178 : Nat := 4983230072969 + 3 ^ 40 * 703178 * 2
def baseEnd_703178 : Nat := 160474799852157798462733

theorem tailTrace_703178 : CollatzResearch.WordTrace tailWord_703178 prefixEnd_703178 160474799852157798462733 := by
  unfold tailWord_703178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411752161628418521599547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17098005764342449390932125 6411752161628418521599547)
  ·
    refine ⟨9617628242442627782399321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6411752161628418521599547 9617628242442627782399321)
    ·
      refine ⟨7213221181831970836799491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9617628242442627782399321 7213221181831970836799491)
      ·
        refine ⟨10819831772747956255199237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7213221181831970836799491 10819831772747956255199237)
        ·
          refine ⟨2028718457390241797849857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10819831772747956255199237 2028718457390241797849857)
          ·
            refine ⟨1521538843042681348387393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2028718457390241797849857 1521538843042681348387393)
            ·
              refine ⟨1141154132282011011290545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521538843042681348387393 1141154132282011011290545)
              ·
                refine ⟨855865599211508258467909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141154132282011011290545 855865599211508258467909)
                ·
                  refine ⟨160474799852157798462733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 855865599211508258467909 160474799852157798462733)
                  ·
                    rfl

theorem cell21_703178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_703178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703178 prefixEnd_703178 := by exact prefixLift 703178
  have htrace : WordTrace (prefixWord ++ tailWord_703178) baseStart_703178 baseEnd_703178 := by
    simpa [prefixWord, tailWord_703178, baseEnd_703178] using wordTrace_append hprefix tailTrace_703178
  have hstable : (prefixWord ++ tailWord_703178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703178).length < 2 ^ (prefixWord ++ tailWord_703178).sum := by decide
  have hdescent : baseEnd_703178 < baseStart_703178 := by decide
  rcases family_descends (prefixWord ++ tailWord_703178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703192 : List Nat := [2, 1, 2, 2, 3, 4, 1, 6]
def baseStart_703192 : Nat := 118140960795 + 703192 * 2 ^ 59
def prefixEnd_703192 : Nat := 4983230072969 + 3 ^ 40 * 703192 * 2
def baseEnd_703192 : Nat := 53492664947632295076457

theorem tailTrace_703192 : CollatzResearch.WordTrace tailWord_703192 prefixEnd_703192 53492664947632295076457 := by
  unfold tailWord_703192
  simp only [CollatzResearch.WordTrace]
  refine ⟨12823759634231477238703915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17098346178975302984938553 12823759634231477238703915)
  ·
    refine ⟨19235639451347215858055873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12823759634231477238703915 19235639451347215858055873)
    ·
      refine ⟨14426729588510411893541905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19235639451347215858055873 14426729588510411893541905)
      ·
        refine ⟨10820047191382808920156429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14426729588510411893541905 10820047191382808920156429)
        ·
          refine ⟨4057517696768553345058661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10820047191382808920156429 4057517696768553345058661)
          ·
            refine ⟨760784568144103752198499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4057517696768553345058661 760784568144103752198499)
            ·
              refine ⟨1141176852216155628297749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760784568144103752198499 1141176852216155628297749)
              ·
                refine ⟨53492664947632295076457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1141176852216155628297749 53492664947632295076457)
                ·
                  rfl

theorem cell21_703192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_703192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703192 prefixEnd_703192 := by exact prefixLift 703192
  have htrace : WordTrace (prefixWord ++ tailWord_703192) baseStart_703192 baseEnd_703192 := by
    simpa [prefixWord, tailWord_703192, baseEnd_703192] using wordTrace_append hprefix tailTrace_703192
  have hstable : (prefixWord ++ tailWord_703192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703192).length < 2 ^ (prefixWord ++ tailWord_703192).sum := by decide
  have hdescent : baseEnd_703192 < baseStart_703192 := by decide
  rcases family_descends (prefixWord ++ tailWord_703192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703268 : List Nat := [2, 3, 1, 3, 3, 1, 1, 7]
def baseStart_703268 : Nat := 118140960795 + 703268 * 2 ^ 59
def prefixEnd_703268 : Nat := 4983230072969 + 3 ^ 40 * 703268 * 2
def baseEnd_703268 : Nat := 53498446359445880654183

theorem tailTrace_703268 : CollatzResearch.WordTrace tailWord_703268 prefixEnd_703268 53498446359445880654183 := by
  unfold tailWord_703268
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825145608093809728587229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17100194144125079638116305 12825145608093809728587229)
  ·
    refine ⟨4809429603035178648220211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12825145608093809728587229 4809429603035178648220211)
    ·
      refine ⟨7214144404552767972330317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4809429603035178648220211 7214144404552767972330317)
      ·
        refine ⟨2705304151707287989623869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7214144404552767972330317 2705304151707287989623869)
        ·
          refine ⟨1014489056890232996108951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2705304151707287989623869 1014489056890232996108951)
          ·
            refine ⟨1521733585335349494163427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014489056890232996108951 1521733585335349494163427)
            ·
              refine ⟨2282600378003024241245141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521733585335349494163427 2282600378003024241245141)
              ·
                refine ⟨53498446359445880654183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2282600378003024241245141 53498446359445880654183)
                ·
                  rfl

theorem cell21_703268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_703268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703268 prefixEnd_703268 := by exact prefixLift 703268
  have htrace : WordTrace (prefixWord ++ tailWord_703268) baseStart_703268 baseEnd_703268 := by
    simpa [prefixWord, tailWord_703268, baseEnd_703268] using wordTrace_append hprefix tailTrace_703268
  have hstable : (prefixWord ++ tailWord_703268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703268).length < 2 ^ (prefixWord ++ tailWord_703268).sum := by decide
  have hdescent : baseEnd_703268 < baseStart_703268 := by decide
  rcases family_descends (prefixWord ++ tailWord_703268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703274 : List Nat := [3, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_703274 : Nat := 118140960795 + 703274 * 2 ^ 59
def prefixEnd_703274 : Nat := 4983230072969 + 3 ^ 40 * 703274 * 2
def baseEnd_703274 : Nat := 160496708360082964862537

theorem tailTrace_703274 : CollatzResearch.WordTrace tailWord_703274 prefixEnd_703274 160496708360082964862537 := by
  unfold tailWord_703274
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412627513541470620473219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17100340036110588321261917 6412627513541470620473219)
  ·
    refine ⟨9618941270312205930709829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6412627513541470620473219 9618941270312205930709829)
    ·
      refine ⟨1803551488183538612008093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9618941270312205930709829 1803551488183538612008093)
      ·
        refine ⟨676331808068826979503035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1803551488183538612008093 676331808068826979503035)
        ·
          refine ⟨1014497712103240469254553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676331808068826979503035 1014497712103240469254553)
          ·
            refine ⟨760873284077430351940915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1014497712103240469254553 760873284077430351940915)
            ·
              refine ⟨1141309926116145527911373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760873284077430351940915 1141309926116145527911373)
              ·
                refine ⟨427991222293554572966765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1141309926116145527911373 427991222293554572966765)
                ·
                  refine ⟨160496708360082964862537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427991222293554572966765 160496708360082964862537)
                  ·
                    rfl

theorem cell21_703274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_703274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703274 prefixEnd_703274 := by exact prefixLift 703274
  have htrace : WordTrace (prefixWord ++ tailWord_703274) baseStart_703274 baseEnd_703274 := by
    simpa [prefixWord, tailWord_703274, baseEnd_703274] using wordTrace_append hprefix tailTrace_703274
  have hstable : (prefixWord ++ tailWord_703274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703274).length < 2 ^ (prefixWord ++ tailWord_703274).sum := by decide
  have hdescent : baseEnd_703274 < baseStart_703274 := by decide
  rcases family_descends (prefixWord ++ tailWord_703274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703302 : List Nat := [6, 1, 1, 2, 2, 1, 2, 6]
def baseStart_703302 : Nat := 118140960795 + 703302 * 2 ^ 59
def prefixEnd_703302 : Nat := 4983230072969 + 3 ^ 40 * 703302 * 2
def baseEnd_703302 : Nat := 53501032780520379465271

theorem tailTrace_703302 : CollatzResearch.WordTrace tailWord_703302 prefixEnd_703302 53501032780520379465271 := by
  unfold tailWord_703302
  simp only [CollatzResearch.WordTrace]
  refine ⟨801610353064513851997255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17101020865376295509274773 801610353064513851997255)
  ·
    refine ⟨1202415529596770777995883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 801610353064513851997255 1202415529596770777995883)
    ·
      refine ⟨1803623294395156166993825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1202415529596770777995883 1803623294395156166993825)
      ·
        refine ⟨1352717470796367125245369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1803623294395156166993825 1352717470796367125245369)
        ·
          refine ⟨1014538103097275343934027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352717470796367125245369 1014538103097275343934027)
          ·
            refine ⟨1521807154645913015901041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014538103097275343934027 1521807154645913015901041)
            ·
              refine ⟨1141355365984434761925781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521807154645913015901041 1141355365984434761925781)
              ·
                refine ⟨53501032780520379465271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1141355365984434761925781 53501032780520379465271)
                ·
                  rfl

theorem cell21_703302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_703302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703302 prefixEnd_703302 := by exact prefixLift 703302
  have htrace : WordTrace (prefixWord ++ tailWord_703302) baseStart_703302 baseEnd_703302 := by
    simpa [prefixWord, tailWord_703302, baseEnd_703302] using wordTrace_append hprefix tailTrace_703302
  have hstable : (prefixWord ++ tailWord_703302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703302).length < 2 ^ (prefixWord ++ tailWord_703302).sum := by decide
  have hdescent : baseEnd_703302 < baseStart_703302 := by decide
  rcases family_descends (prefixWord ++ tailWord_703302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703350 : List Nat := [5, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_703350 : Nat := 118140960795 + 703350 * 2 ^ 59
def prefixEnd_703350 : Nat := 4983230072969 + 3 ^ 40 * 703350 * 2
def baseEnd_703350 : Nat := 160514052595523721595715

theorem tailTrace_703350 : CollatzResearch.WordTrace tailWord_703350 prefixEnd_703350 160514052595523721595715 := by
  unfold tailWord_703350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1603330125118159216353719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17102188001260364974439669 1603330125118159216353719)
  ·
    refine ⟨2404995187677238824530579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1603330125118159216353719 2404995187677238824530579)
    ·
      refine ⟨3607492781515858236795869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404995187677238824530579 3607492781515858236795869)
      ·
        refine ⟨1352809793068446838798451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3607492781515858236795869 1352809793068446838798451)
        ·
          refine ⟨2029214689602670258197677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352809793068446838798451 2029214689602670258197677)
          ·
            refine ⟨760955508601001346824129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2029214689602670258197677 760955508601001346824129)
            ·
              refine ⟨570716631450751010118097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760955508601001346824129 570716631450751010118097)
              ·
                refine ⟨428037473588063257588573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570716631450751010118097 428037473588063257588573)
                ·
                  refine ⟨160514052595523721595715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428037473588063257588573 160514052595523721595715)
                  ·
                    rfl

theorem cell21_703350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_703350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703350 prefixEnd_703350 := by exact prefixLift 703350
  have htrace : WordTrace (prefixWord ++ tailWord_703350) baseStart_703350 baseEnd_703350 := by
    simpa [prefixWord, tailWord_703350, baseEnd_703350] using wordTrace_append hprefix tailTrace_703350
  have hstable : (prefixWord ++ tailWord_703350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703350).length < 2 ^ (prefixWord ++ tailWord_703350).sum := by decide
  have hdescent : baseEnd_703350 < baseStart_703350 := by decide
  rcases family_descends (prefixWord ++ tailWord_703350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703448 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_703448 : Nat := 118140960795 + 703448 * 2 ^ 59
def prefixEnd_703448 : Nat := 4983230072969 + 3 ^ 40 * 703448 * 2
def baseEnd_703448 : Nat := 160536417530697328962181

theorem tailTrace_703448 : CollatzResearch.WordTrace tailWord_703448 prefixEnd_703448 160536417530697328962181 := by
  unfold tailWord_703448
  simp only [CollatzResearch.WordTrace]
  refine ⟨12828428177767755099363499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17104570903690340132484665 12828428177767755099363499)
  ·
    refine ⟨19242642266651632649045249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12828428177767755099363499 19242642266651632649045249)
    ·
      refine ⟨14431981699988724486783937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19242642266651632649045249 14431981699988724486783937)
      ·
        refine ⟨10823986274991543365087953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14431981699988724486783937 10823986274991543365087953)
        ·
          refine ⟨8117989706243657523815965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10823986274991543365087953 8117989706243657523815965)
          ·
            refine ⟨3044246139841371571430987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8117989706243657523815965 3044246139841371571430987)
            ·
              refine ⟨4566369209762057357146481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044246139841371571430987 4566369209762057357146481)
              ·
                refine ⟨3424776907321543017859861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4566369209762057357146481 3424776907321543017859861)
                ·
                  refine ⟨160536417530697328962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3424776907321543017859861 160536417530697328962181)
                  ·
                    rfl

theorem cell21_703448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_703448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703448 prefixEnd_703448 := by exact prefixLift 703448
  have htrace : WordTrace (prefixWord ++ tailWord_703448) baseStart_703448 baseEnd_703448 := by
    simpa [prefixWord, tailWord_703448, baseEnd_703448] using wordTrace_append hprefix tailTrace_703448
  have hstable : (prefixWord ++ tailWord_703448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703448).length < 2 ^ (prefixWord ++ tailWord_703448).sum := by decide
  have hdescent : baseEnd_703448 < baseStart_703448 := by decide
  rcases family_descends (prefixWord ++ tailWord_703448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703493 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 7]
def baseStart_703493 : Nat := 118140960795 + 703493 * 2 ^ 59
def prefixEnd_703493 : Nat := 4983230072969 + 3 ^ 40 * 703493 * 2
def baseEnd_703493 : Nat := 160546687143787250712089

theorem tailTrace_703493 : CollatzResearch.WordTrace tailWord_703493 prefixEnd_703493 160546687143787250712089 := by
  unfold tailWord_703493
  simp only [CollatzResearch.WordTrace]
  refine ⟨25658497640372482884115133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17105665093581655256076755 25658497640372482884115133)
  ·
    refine ⟨9621936615139681081543175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25658497640372482884115133 9621936615139681081543175)
    ·
      refine ⟨14432904922709521622314763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9621936615139681081543175 14432904922709521622314763)
      ·
        refine ⟨21649357384064282433472145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14432904922709521622314763 21649357384064282433472145)
        ·
          refine ⟨16237018038048211825104109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21649357384064282433472145 16237018038048211825104109)
          ·
            refine ⟨6088881764268079434414041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16237018038048211825104109 6088881764268079434414041)
            ·
              refine ⟨4566661323201059575810531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6088881764268079434414041 4566661323201059575810531)
              ·
                refine ⟨6849991984801589363715797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566661323201059575810531 6849991984801589363715797)
                ·
                  refine ⟨160546687143787250712089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6849991984801589363715797 160546687143787250712089)
                  ·
                    rfl

theorem cell21_703493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_703493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703493 prefixEnd_703493 := by exact prefixLift 703493
  have htrace : WordTrace (prefixWord ++ tailWord_703493) baseStart_703493 baseEnd_703493 := by
    simpa [prefixWord, tailWord_703493, baseEnd_703493] using wordTrace_append hprefix tailTrace_703493
  have hstable : (prefixWord ++ tailWord_703493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703493).length < 2 ^ (prefixWord ++ tailWord_703493).sum := by decide
  have hdescent : baseEnd_703493 < baseStart_703493 := by decide
  rcases family_descends (prefixWord ++ tailWord_703493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703555 : List Nat := [1, 1, 1, 3, 1, 2, 7, 5]
def baseStart_703555 : Nat := 118140960795 + 703555 * 2 ^ 59
def prefixEnd_703555 : Nat := 4983230072969 + 3 ^ 40 * 703555 * 2
def baseEnd_703555 : Nat := 53520278796162973559543

theorem tailTrace_703555 : CollatzResearch.WordTrace tailWord_703555 prefixEnd_703555 53520278796162973559543 := by
  unfold tailWord_703555
  simp only [CollatzResearch.WordTrace]
  refine ⟨25660758966147867472872119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17107172644098578315248079 25660758966147867472872119)
  ·
    refine ⟨38491138449221801209308179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25660758966147867472872119 38491138449221801209308179)
    ·
      refine ⟨57736707673832701813962269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38491138449221801209308179 57736707673832701813962269)
      ·
        refine ⟨21651265377687263180235851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57736707673832701813962269 21651265377687263180235851)
        ·
          refine ⟨32476898066530894770353777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21651265377687263180235851 32476898066530894770353777)
          ·
            refine ⟨24357673549898171077765333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32476898066530894770353777 24357673549898171077765333)
            ·
              refine ⟨570882973825738384635125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24357673549898171077765333 570882973825738384635125)
              ·
                refine ⟨53520278796162973559543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 570882973825738384635125 53520278796162973559543)
                ·
                  rfl

theorem cell21_703555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 5].length) (baseStart_703555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703555 prefixEnd_703555 := by exact prefixLift 703555
  have htrace : WordTrace (prefixWord ++ tailWord_703555) baseStart_703555 baseEnd_703555 := by
    simpa [prefixWord, tailWord_703555, baseEnd_703555] using wordTrace_append hprefix tailTrace_703555
  have hstable : (prefixWord ++ tailWord_703555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703555).length < 2 ^ (prefixWord ++ tailWord_703555).sum := by decide
  have hdescent : baseEnd_703555 < baseStart_703555 := by decide
  rcases family_descends (prefixWord ++ tailWord_703555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703620 : List Nat := [2, 3, 2, 1, 2, 4, 1, 3, 3]
def baseStart_703620 : Nat := 118140960795 + 703620 * 2 ^ 59
def prefixEnd_703620 : Nat := 4983230072969 + 3 ^ 40 * 703620 * 2
def baseEnd_703620 : Nat := 160575670274063252095163

theorem tailTrace_703620 : CollatzResearch.WordTrace tailWord_703620 prefixEnd_703620 160575670274063252095163 := by
  unfold tailWord_703620
  simp only [CollatzResearch.WordTrace]
  refine ⟨12831564855456191786994157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17108753140608255715992209 12831564855456191786994157)
  ·
    refine ⟨4811836820796071920122809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12831564855456191786994157 4811836820796071920122809)
    ·
      refine ⟨3608877615597053940092107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4811836820796071920122809 3608877615597053940092107)
      ·
        refine ⟨5413316423395580910138161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608877615597053940092107 5413316423395580910138161)
        ·
          refine ⟨4059987317546685682603621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5413316423395580910138161 4059987317546685682603621)
          ·
            refine ⟨761247622040003565488179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4059987317546685682603621 761247622040003565488179)
            ·
              refine ⟨1141871433060005348232269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761247622040003565488179 1141871433060005348232269)
              ·
                refine ⟨428201787397502005587101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1141871433060005348232269 428201787397502005587101)
                ·
                  refine ⟨160575670274063252095163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428201787397502005587101 160575670274063252095163)
                  ·
                    rfl

theorem cell21_703620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_703620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703620 prefixEnd_703620 := by exact prefixLift 703620
  have htrace : WordTrace (prefixWord ++ tailWord_703620) baseStart_703620 baseEnd_703620 := by
    simpa [prefixWord, tailWord_703620, baseEnd_703620] using wordTrace_append hprefix tailTrace_703620
  have hstable : (prefixWord ++ tailWord_703620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703620).length < 2 ^ (prefixWord ++ tailWord_703620).sum := by decide
  have hdescent : baseEnd_703620 < baseStart_703620 := by decide
  rcases family_descends (prefixWord ++ tailWord_703620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703690 : List Nat := [3, 1, 2, 1, 3, 11]
def baseStart_703690 : Nat := 118140960795 + 703690 * 2 ^ 59
def prefixEnd_703690 : Nat := 4983230072969 + 3 ^ 40 * 703690 * 2
def baseEnd_703690 : Nat := 5947838712139210589939

theorem tailTrace_703690 : CollatzResearch.WordTrace tailWord_703690 prefixEnd_703690 5947838712139210589939 := by
  unfold tailWord_703690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416420705164696382259131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17110455213772523686024349 6416420705164696382259131)
  ·
    refine ⟨9624631057747044573388697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6416420705164696382259131 9624631057747044573388697)
    ·
      refine ⟨7218473293310283430041523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9624631057747044573388697 7218473293310283430041523)
      ·
        refine ⟨10827709939965425145062285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7218473293310283430041523 10827709939965425145062285)
        ·
          refine ⟨4060391227487034429398357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10827709939965425145062285 4060391227487034429398357)
          ·
            refine ⟨5947838712139210589939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4060391227487034429398357 5947838712139210589939)
            ·
              rfl

theorem cell21_703690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 11].length) (baseStart_703690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703690 prefixEnd_703690 := by exact prefixLift 703690
  have htrace : WordTrace (prefixWord ++ tailWord_703690) baseStart_703690 baseEnd_703690 := by
    simpa [prefixWord, tailWord_703690, baseEnd_703690] using wordTrace_append hprefix tailTrace_703690
  have hstable : (prefixWord ++ tailWord_703690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703690).length < 2 ^ (prefixWord ++ tailWord_703690).sum := by decide
  have hdescent : baseEnd_703690 < baseStart_703690 := by decide
  rcases family_descends (prefixWord ++ tailWord_703690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703735 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 8]
def baseStart_703735 : Nat := 118140960795 + 703735 * 2 ^ 59
def prefixEnd_703735 : Nat := 4983230072969 + 3 ^ 40 * 703735 * 2
def baseEnd_703735 : Nat := 160601914840848607678261

theorem tailTrace_703735 : CollatzResearch.WordTrace tailWord_703735 prefixEnd_703735 160601914840848607678261 := by
  unfold tailWord_703735
  simp only [CollatzResearch.WordTrace]
  refine ⟨25667324105495758214424659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17111549403663838809616439 25667324105495758214424659)
  ·
    refine ⟨38500986158243637321636989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25667324105495758214424659 38500986158243637321636989)
    ·
      refine ⟨14437869809341363995613871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38500986158243637321636989 14437869809341363995613871)
      ·
        refine ⟨21656804714012045993420807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14437869809341363995613871 21656804714012045993420807)
        ·
          refine ⟨32485207071018068990131211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21656804714012045993420807 32485207071018068990131211)
          ·
            refine ⟨48727810606527103485196817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32485207071018068990131211 48727810606527103485196817)
            ·
              refine ⟨36545857954895327613897613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48727810606527103485196817 36545857954895327613897613)
              ·
                refine ⟨13704696733085747855211605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36545857954895327613897613 13704696733085747855211605)
                ·
                  refine ⟨160601914840848607678261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13704696733085747855211605 160601914840848607678261)
                  ·
                    rfl

theorem cell21_703735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_703735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703735 prefixEnd_703735 := by exact prefixLift 703735
  have htrace : WordTrace (prefixWord ++ tailWord_703735) baseStart_703735 baseEnd_703735 := by
    simpa [prefixWord, tailWord_703735, baseEnd_703735] using wordTrace_append hprefix tailTrace_703735
  have hstable : (prefixWord ++ tailWord_703735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703735).length < 2 ^ (prefixWord ++ tailWord_703735).sum := by decide
  have hdescent : baseEnd_703735 < baseStart_703735 := by decide
  rcases family_descends (prefixWord ++ tailWord_703735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703789 : List Nat := [1, 5, 3, 1, 1, 3, 1, 3, 3]
def baseStart_703789 : Nat := 118140960795 + 703789 * 2 ^ 59
def prefixEnd_703789 : Nat := 4983230072969 + 3 ^ 40 * 703789 * 2
def baseEnd_703789 : Nat := 160614238376556513778151

theorem tailTrace_703789 : CollatzResearch.WordTrace tailWord_703789 prefixEnd_703789 160614238376556513778151 := by
  unfold tailWord_703789
  simp only [CollatzResearch.WordTrace]
  refine ⟨25669293647300125436890421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17112862431533416957926947 25669293647300125436890421)
  ·
    refine ⟨2406496279434386759708477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25669293647300125436890421 2406496279434386759708477)
    ·
      refine ⟨902436104787895034890679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2406496279434386759708477 902436104787895034890679)
      ·
        refine ⟨1353654157181842552336019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902436104787895034890679 1353654157181842552336019)
        ·
          refine ⟨2030481235772763828504029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353654157181842552336019 2030481235772763828504029)
          ·
            refine ⟨761430463414786435689011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2030481235772763828504029 761430463414786435689011)
            ·
              refine ⟨1142145695122179653533517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761430463414786435689011 1142145695122179653533517)
              ·
                refine ⟨428304635670817370075069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142145695122179653533517 428304635670817370075069)
                ·
                  refine ⟨160614238376556513778151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428304635670817370075069 160614238376556513778151)
                  ·
                    rfl

theorem cell21_703789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_703789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703789 prefixEnd_703789 := by exact prefixLift 703789
  have htrace : WordTrace (prefixWord ++ tailWord_703789) baseStart_703789 baseEnd_703789 := by
    simpa [prefixWord, tailWord_703789, baseEnd_703789] using wordTrace_append hprefix tailTrace_703789
  have hstable : (prefixWord ++ tailWord_703789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703789).length < 2 ^ (prefixWord ++ tailWord_703789).sum := by decide
  have hdescent : baseEnd_703789 < baseStart_703789 := by decide
  rcases family_descends (prefixWord ++ tailWord_703789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703994 : List Nat := [3, 1, 1, 1, 1, 2, 6, 6]
def baseStart_703994 : Nat := 118140960795 + 703994 * 2 ^ 59
def prefixEnd_703994 : Nat := 4983230072969 + 3 ^ 40 * 703994 * 2
def baseEnd_703994 : Nat := 53553674056507237620355

theorem tailTrace_703994 : CollatzResearch.WordTrace tailWord_703994 prefixEnd_703994 53553674056507237620355 := by
  unfold tailWord_703994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419192652889361362025759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17117847074371630298735357 6419192652889361362025759)
  ·
    refine ⟨9628788979334042043038639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6419192652889361362025759 9628788979334042043038639)
    ·
      refine ⟨14443183469001063064557959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9628788979334042043038639 14443183469001063064557959)
      ·
        refine ⟨21664775203501594596836939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14443183469001063064557959 21664775203501594596836939)
        ·
          refine ⟨32497162805252391895255409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21664775203501594596836939 32497162805252391895255409)
          ·
            refine ⟨24372872103939293921441557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32497162805252391895255409 24372872103939293921441557)
            ·
              refine ⟨1142478379872154402567573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24372872103939293921441557 1142478379872154402567573)
              ·
                refine ⟨53553674056507237620355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1142478379872154402567573 53553674056507237620355)
                ·
                  rfl

theorem cell21_703994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_703994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703994 prefixEnd_703994 := by exact prefixLift 703994
  have htrace : WordTrace (prefixWord ++ tailWord_703994) baseStart_703994 baseEnd_703994 := by
    simpa [prefixWord, tailWord_703994, baseEnd_703994] using wordTrace_append hprefix tailTrace_703994
  have hstable : (prefixWord ++ tailWord_703994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703994).length < 2 ^ (prefixWord ++ tailWord_703994).sum := by decide
  have hdescent : baseEnd_703994 < baseStart_703994 := by decide
  rcases family_descends (prefixWord ++ tailWord_703994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_703997 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 4]
def baseStart_703997 : Nat := 118140960795 + 703997 * 2 ^ 59
def prefixEnd_703997 : Nat := 4983230072969 + 3 ^ 40 * 703997 * 2
def baseEnd_703997 : Nat := 160661706810394374311059

theorem tailTrace_703997 : CollatzResearch.WordTrace tailWord_703997 prefixEnd_703997 160661706810394374311059 := by
  unfold tailWord_703997
  simp only [CollatzResearch.WordTrace]
  refine ⟨25676880030546576960462245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17117920020364384640308163 25676880030546576960462245)
  ·
    refine ⟨4814415005727483180086671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25676880030546576960462245 4814415005727483180086671)
    ·
      refine ⟨7221622508591224770130007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4814415005727483180086671 7221622508591224770130007)
      ·
        refine ⟨10832433762886837155195011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7221622508591224770130007 10832433762886837155195011)
        ·
          refine ⟨16248650644330255732792517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10832433762886837155195011 16248650644330255732792517)
          ·
            refine ⟨3046621995811922949898597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16248650644330255732792517 3046621995811922949898597)
            ·
              refine ⟨571241624214735553105987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3046621995811922949898597 571241624214735553105987)
              ·
                refine ⟨856862436322103329658981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571241624214735553105987 856862436322103329658981)
                ·
                  refine ⟨160661706810394374311059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 856862436322103329658981 160661706810394374311059)
                  ·
                    rfl

theorem cell21_703997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_703997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_703997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_703997 prefixEnd_703997 := by exact prefixLift 703997
  have htrace : WordTrace (prefixWord ++ tailWord_703997) baseStart_703997 baseEnd_703997 := by
    simpa [prefixWord, tailWord_703997, baseEnd_703997] using wordTrace_append hprefix tailTrace_703997
  have hstable : (prefixWord ++ tailWord_703997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_703997).length < 2 ^ (prefixWord ++ tailWord_703997).sum := by decide
  have hdescent : baseEnd_703997 < baseStart_703997 := by decide
  rcases family_descends (prefixWord ++ tailWord_703997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704056 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_704056 : Nat := 118140960795 + 704056 * 2 ^ 59
def prefixEnd_704056 : Nat := 4983230072969 + 3 ^ 40 * 704056 * 2
def baseEnd_704056 : Nat := 160675171414223382827605

theorem tailTrace_704056 : CollatzResearch.WordTrace tailWord_704056 prefixEnd_704056 160675171414223382827605 := by
  unfold tailWord_704056
  simp only [CollatzResearch.WordTrace]
  refine ⟨12839515968666415018430011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17119354624888553357906681 12839515968666415018430011)
  ·
    refine ⟨19259273952999622527645017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12839515968666415018430011 19259273952999622527645017)
    ·
      refine ⟨14444455464749716895733763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19259273952999622527645017 14444455464749716895733763)
      ·
        refine ⟨21666683197124575343600645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14444455464749716895733763 21666683197124575343600645)
        ·
          refine ⟨4062503099460857876925121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21666683197124575343600645 4062503099460857876925121)
          ·
            refine ⟨3046877324595643407693841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4062503099460857876925121 3046877324595643407693841)
            ·
              refine ⟨2285157993446732555770381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046877324595643407693841 2285157993446732555770381)
              ·
                refine ⟨856934247542524708413893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2285157993446732555770381 856934247542524708413893)
                ·
                  refine ⟨160675171414223382827605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 856934247542524708413893 160675171414223382827605)
                  ·
                    rfl

theorem cell21_704056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_704056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704056 prefixEnd_704056 := by exact prefixLift 704056
  have htrace : WordTrace (prefixWord ++ tailWord_704056) baseStart_704056 baseEnd_704056 := by
    simpa [prefixWord, tailWord_704056, baseEnd_704056] using wordTrace_append hprefix tailTrace_704056
  have hstable : (prefixWord ++ tailWord_704056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704056).length < 2 ^ (prefixWord ++ tailWord_704056).sum := by decide
  have hdescent : baseEnd_704056 < baseStart_704056 := by decide
  rcases family_descends (prefixWord ++ tailWord_704056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704101 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 5]
def baseStart_704101 : Nat := 118140960795 + 704101 * 2 ^ 59
def prefixEnd_704101 : Nat := 4983230072969 + 3 ^ 40 * 704101 * 2
def baseEnd_704101 : Nat := 160685441027313304577513

theorem tailTrace_704101 : CollatzResearch.WordTrace tailWord_704101 prefixEnd_704101 160685441027313304577513 := by
  unfold tailWord_704101
  simp only [CollatzResearch.WordTrace]
  refine ⟨25680673222169802722248157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17120448814779868481498771 25680673222169802722248157)
  ·
    refine ⟨9630252458313676020843059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25680673222169802722248157 9630252458313676020843059)
    ·
      refine ⟨14445378687470514031264589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9630252458313676020843059 14445378687470514031264589)
      ·
        refine ⟨5417017007801442761724221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14445378687470514031264589 5417017007801442761724221)
        ·
          refine ⟨2031381377925541035646583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5417017007801442761724221 2031381377925541035646583)
          ·
            refine ⟨3047072066888311553469875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031381377925541035646583 3047072066888311553469875)
            ·
              refine ⟨4570608100332467330204813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047072066888311553469875 4570608100332467330204813)
              ·
                refine ⟨1713978037624675248826805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4570608100332467330204813 1713978037624675248826805)
                ·
                  refine ⟨160685441027313304577513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1713978037624675248826805 160685441027313304577513)
                  ·
                    rfl

theorem cell21_704101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_704101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704101 prefixEnd_704101 := by exact prefixLift 704101
  have htrace : WordTrace (prefixWord ++ tailWord_704101) baseStart_704101 baseEnd_704101 := by
    simpa [prefixWord, tailWord_704101, baseEnd_704101] using wordTrace_append hprefix tailTrace_704101
  have hstable : (prefixWord ++ tailWord_704101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704101).length < 2 ^ (prefixWord ++ tailWord_704101).sum := by decide
  have hdescent : baseEnd_704101 < baseStart_704101 := by decide
  rcases family_descends (prefixWord ++ tailWord_704101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704118 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_704118 : Nat := 118140960795 + 704118 * 2 ^ 59
def prefixEnd_704118 : Nat := 4983230072969 + 3 ^ 40 * 704118 * 2
def baseEnd_704118 : Nat := 160689320658925052794145

theorem tailTrace_704118 : CollatzResearch.WordTrace tailWord_704118 prefixEnd_704118 160689320658925052794145 := by
  unfold tailWord_704118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605080828944263414101063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17120862175405476417078005 1605080828944263414101063)
  ·
    refine ⟨2407621243416395121151595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605080828944263414101063 2407621243416395121151595)
    ·
      refine ⟨3611431865124592681727393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2407621243416395121151595 3611431865124592681727393)
      ·
        refine ⟨2708573898843444511295545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3611431865124592681727393 2708573898843444511295545)
        ·
          refine ⟨2031430424132583383471659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2708573898843444511295545 2031430424132583383471659)
          ·
            refine ⟨3047145636198875075207489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031430424132583383471659 3047145636198875075207489)
            ·
              refine ⟨2285359227149156306405617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3047145636198875075207489 2285359227149156306405617)
              ·
                refine ⟨1714019420361867229804213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285359227149156306405617 1714019420361867229804213)
                ·
                  refine ⟨160689320658925052794145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1714019420361867229804213 160689320658925052794145)
                  ·
                    rfl

theorem cell21_704118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_704118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704118 prefixEnd_704118 := by exact prefixLift 704118
  have htrace : WordTrace (prefixWord ++ tailWord_704118) baseStart_704118 baseEnd_704118 := by
    simpa [prefixWord, tailWord_704118, baseEnd_704118] using wordTrace_append hprefix tailTrace_704118
  have hstable : (prefixWord ++ tailWord_704118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704118).length < 2 ^ (prefixWord ++ tailWord_704118).sum := by decide
  have hdescent : baseEnd_704118 < baseStart_704118 := by decide
  rcases family_descends (prefixWord ++ tailWord_704118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704135 : List Nat := [1, 1, 4, 2, 1, 5, 1, 3, 3]
def baseStart_704135 : Nat := 118140960795 + 704135 * 2 ^ 59
def prefixEnd_704135 : Nat := 4983230072969 + 3 ^ 40 * 704135 * 2
def baseEnd_704135 : Nat := 160693200290536801010777

theorem tailTrace_704135 : CollatzResearch.WordTrace tailWord_704135 prefixEnd_704135 160693200290536801010777 := by
  unfold tailWord_704135
  simp only [CollatzResearch.WordTrace]
  refine ⟨25681913304046626528985859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17121275536031084352657239 25681913304046626528985859)
  ·
    refine ⟨38522869956069939793478789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25681913304046626528985859 38522869956069939793478789)
    ·
      refine ⟨7223038116763113711277273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38522869956069939793478789 7223038116763113711277273)
      ·
        refine ⟨5417278587572335283457955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7223038116763113711277273 5417278587572335283457955)
        ·
          refine ⟨8125917881358502925186933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5417278587572335283457955 8125917881358502925186933)
          ·
            refine ⟨761804801377359649236275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8125917881358502925186933 761804801377359649236275)
            ·
              refine ⟨1142707202066039473854413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761804801377359649236275 1142707202066039473854413)
              ·
                refine ⟨428515200774764802695405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142707202066039473854413 428515200774764802695405)
                ·
                  refine ⟨160693200290536801010777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428515200774764802695405 160693200290536801010777)
                  ·
                    rfl

theorem cell21_704135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 3].length) (baseStart_704135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704135 prefixEnd_704135 := by exact prefixLift 704135
  have htrace : WordTrace (prefixWord ++ tailWord_704135) baseStart_704135 baseEnd_704135 := by
    simpa [prefixWord, tailWord_704135, baseEnd_704135] using wordTrace_append hprefix tailTrace_704135
  have hstable : (prefixWord ++ tailWord_704135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704135).length < 2 ^ (prefixWord ++ tailWord_704135).sum := by decide
  have hdescent : baseEnd_704135 < baseStart_704135 := by decide
  rcases family_descends (prefixWord ++ tailWord_704135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704214 : List Nat := [5, 2, 1, 3, 2, 1, 1, 6]
def baseStart_704214 : Nat := 118140960795 + 704214 * 2 ^ 59
def prefixEnd_704214 : Nat := 4983230072969 + 3 ^ 40 * 704214 * 2
def baseEnd_704214 : Nat := 53570409722283406397983

theorem tailTrace_704214 : CollatzResearch.WordTrace tailWord_704214 prefixEnd_704214 53570409722283406397983 := by
  unfold tailWord_704214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605299666922526438819481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17123196447173615347407797 1605299666922526438819481)
  ·
    refine ⟨1203974750191894829114611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1605299666922526438819481 1203974750191894829114611)
    ·
      refine ⟨1805962125287842243671917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203974750191894829114611 1805962125287842243671917)
      ·
        refine ⟨677235796982940841376969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1805962125287842243671917 677235796982940841376969)
        ·
          refine ⟨507926847737205631032727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677235796982940841376969 507926847737205631032727)
          ·
            refine ⟨761890271605808446549091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507926847737205631032727 761890271605808446549091)
            ·
              refine ⟨1142835407408712669823637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761890271605808446549091 1142835407408712669823637)
              ·
                refine ⟨53570409722283406397983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1142835407408712669823637 53570409722283406397983)
                ·
                  rfl

theorem cell21_704214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_704214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704214 prefixEnd_704214 := by exact prefixLift 704214
  have htrace : WordTrace (prefixWord ++ tailWord_704214) baseStart_704214 baseEnd_704214 := by
    simpa [prefixWord, tailWord_704214, baseEnd_704214] using wordTrace_append hprefix tailTrace_704214
  have hstable : (prefixWord ++ tailWord_704214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704214).length < 2 ^ (prefixWord ++ tailWord_704214).sum := by decide
  have hdescent : baseEnd_704214 < baseStart_704214 := by decide
  rcases family_descends (prefixWord ++ tailWord_704214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704236 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_704236 : Nat := 118140960795 + 704236 * 2 ^ 59
def prefixEnd_704236 : Nat := 4983230072969 + 3 ^ 40 * 704236 * 2
def baseEnd_704236 : Nat := 160716249866583069827237

theorem tailTrace_704236 : CollatzResearch.WordTrace tailWord_704236 prefixEnd_704236 160716249866583069827237 := by
  unfold tailWord_704236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12842798538340360389206281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17123731384453813852275041 12842798538340360389206281)
  ·
    refine ⟨9632098903755270291904711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12842798538340360389206281 9632098903755270291904711)
    ·
      refine ⟨14448148355632905437857067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9632098903755270291904711 14448148355632905437857067)
      ·
        refine ⟨21672222533449358156785601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14448148355632905437857067 21672222533449358156785601)
        ·
          refine ⟨16254166900087018617589201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21672222533449358156785601 16254166900087018617589201)
          ·
            refine ⟨12190625175065263963191901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16254166900087018617589201 12190625175065263963191901)
            ·
              refine ⟨4571484440649473986196963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12190625175065263963191901 4571484440649473986196963)
              ·
                refine ⟨6857226660974210979295445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571484440649473986196963 6857226660974210979295445)
                ·
                  refine ⟨160716249866583069827237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6857226660974210979295445 160716249866583069827237)
                  ·
                    rfl

theorem cell21_704236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_704236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704236 prefixEnd_704236 := by exact prefixLift 704236
  have htrace : WordTrace (prefixWord ++ tailWord_704236) baseStart_704236 baseEnd_704236 := by
    simpa [prefixWord, tailWord_704236, baseEnd_704236] using wordTrace_append hprefix tailTrace_704236
  have hstable : (prefixWord ++ tailWord_704236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704236).length < 2 ^ (prefixWord ++ tailWord_704236).sum := by decide
  have hdescent : baseEnd_704236 < baseStart_704236 := by decide
  rcases family_descends (prefixWord ++ tailWord_704236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704262 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_704262 : Nat := 118140960795 + 704262 * 2 ^ 59
def prefixEnd_704262 : Nat := 4983230072969 + 3 ^ 40 * 704262 * 2
def baseEnd_704262 : Nat := 160722183420812802393851

theorem tailTrace_704262 : CollatzResearch.WordTrace tailWord_704262 prefixEnd_704262 160722183420812802393851 := by
  unfold tailWord_704262
  simp only [CollatzResearch.WordTrace]
  refine ⟨802704542955828975589345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17124363583057684812572693 802704542955828975589345)
  ·
    refine ⟨602028407216871731692009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 802704542955828975589345 602028407216871731692009)
    ·
      refine ⟨451521305412653798769007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 602028407216871731692009 451521305412653798769007)
      ·
        refine ⟨677281958118980698153511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451521305412653798769007 677281958118980698153511)
        ·
          refine ⟨1015922937178471047230267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677281958118980698153511 1015922937178471047230267)
          ·
            refine ⟨1523884405767706570845401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015922937178471047230267 1523884405767706570845401)
            ·
              refine ⟨1142913304325779928134051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523884405767706570845401 1142913304325779928134051)
              ·
                refine ⟨1714369956488669892201077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142913304325779928134051 1714369956488669892201077)
                ·
                  refine ⟨160722183420812802393851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1714369956488669892201077 160722183420812802393851)
                  ·
                    rfl

theorem cell21_704262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_704262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704262 prefixEnd_704262 := by exact prefixLift 704262
  have htrace : WordTrace (prefixWord ++ tailWord_704262) baseStart_704262 baseEnd_704262 := by
    simpa [prefixWord, tailWord_704262, baseEnd_704262] using wordTrace_append hprefix tailTrace_704262
  have hstable : (prefixWord ++ tailWord_704262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704262).length < 2 ^ (prefixWord ++ tailWord_704262).sum := by decide
  have hdescent : baseEnd_704262 < baseStart_704262 := by decide
  rcases family_descends (prefixWord ++ tailWord_704262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704270 : List Nat := [4, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_704270 : Nat := 118140960795 + 704270 * 2 ^ 59
def prefixEnd_704270 : Nat := 4983230072969 + 3 ^ 40 * 704270 * 2
def baseEnd_704270 : Nat := 160724009129806566260501

theorem tailTrace_704270 : CollatzResearch.WordTrace tailWord_704270 prefixEnd_704270 160724009129806566260501 := by
  unfold tailWord_704270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210854644819693073143783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17124558105705029723433509 3210854644819693073143783)
  ·
    refine ⟨4816281967229539609715675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3210854644819693073143783 4816281967229539609715675)
    ·
      refine ⟨7224422950844309414573513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4816281967229539609715675 7224422950844309414573513)
      ·
        refine ⟨5418317213133232060930135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7224422950844309414573513 5418317213133232060930135)
        ·
          refine ⟨8127475819699848091395203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5418317213133232060930135 8127475819699848091395203)
          ·
            refine ⟨12191213729549772137092805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8127475819699848091395203 12191213729549772137092805)
            ·
              refine ⟨2285852574290582275704901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12191213729549772137092805 2285852574290582275704901)
              ·
                refine ⟨428597357679484176694669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2285852574290582275704901 428597357679484176694669)
                ·
                  refine ⟨160724009129806566260501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428597357679484176694669 160724009129806566260501)
                  ·
                    rfl

theorem cell21_704270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_704270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704270 prefixEnd_704270 := by exact prefixLift 704270
  have htrace : WordTrace (prefixWord ++ tailWord_704270) baseStart_704270 baseEnd_704270 := by
    simpa [prefixWord, tailWord_704270, baseEnd_704270] using wordTrace_append hprefix tailTrace_704270
  have hstable : (prefixWord ++ tailWord_704270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704270).length < 2 ^ (prefixWord ++ tailWord_704270).sum := by decide
  have hdescent : baseEnd_704270 < baseStart_704270 := by decide
  rcases family_descends (prefixWord ++ tailWord_704270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704276 : List Nat := [2, 4, 4, 1, 1, 1, 3, 1, 4]
def baseStart_704276 : Nat := 118140960795 + 704276 * 2 ^ 59
def prefixEnd_704276 : Nat := 4983230072969 + 3 ^ 40 * 704276 * 2
def baseEnd_704276 : Nat := 160725378411551889160489

theorem tailTrace_704276 : CollatzResearch.WordTrace tailWord_704276 prefixEnd_704276 160725378411551889160489 := by
  unfold tailWord_704276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12843527998267903804934341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17124703997690538406579121 12843527998267903804934341)
  ·
    refine ⟨2408161499675231963425189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12843527998267903804934341 2408161499675231963425189)
    ·
      refine ⟨451530281189105993142223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2408161499675231963425189 451530281189105993142223)
      ·
        refine ⟨677295421783658989713335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451530281189105993142223 677295421783658989713335)
        ·
          refine ⟨1015943132675488484570003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677295421783658989713335 1015943132675488484570003)
          ·
            refine ⟨1523914699013232726855005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015943132675488484570003 1523914699013232726855005)
            ·
              refine ⟨571468012129962272570627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1523914699013232726855005 571468012129962272570627)
              ·
                refine ⟨857202018194943408855941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571468012129962272570627 857202018194943408855941)
                ·
                  refine ⟨160725378411551889160489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857202018194943408855941 160725378411551889160489)
                  ·
                    rfl

theorem cell21_704276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_704276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704276 prefixEnd_704276 := by exact prefixLift 704276
  have htrace : WordTrace (prefixWord ++ tailWord_704276) baseStart_704276 baseEnd_704276 := by
    simpa [prefixWord, tailWord_704276, baseEnd_704276] using wordTrace_append hprefix tailTrace_704276
  have hstable : (prefixWord ++ tailWord_704276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704276).length < 2 ^ (prefixWord ++ tailWord_704276).sum := by decide
  have hdescent : baseEnd_704276 < baseStart_704276 := by decide
  rcases family_descends (prefixWord ++ tailWord_704276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704374 : List Nat := [5, 1, 1, 3, 11]
def baseStart_704374 : Nat := 118140960795 + 704374 * 2 ^ 59
def prefixEnd_704374 : Nat := 4983230072969 + 3 ^ 40 * 704374 * 2
def baseEnd_704374 : Nat := 1984540041317598722555

theorem tailTrace_704374 : CollatzResearch.WordTrace tailWord_704374 prefixEnd_704374 1984540041317598722555 := by
  unfold tailWord_704374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605664396886298146683511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17127086900120513564624117 1605664396886298146683511)
  ·
    refine ⟨2408496595329447220025267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605664396886298146683511 2408496595329447220025267)
    ·
      refine ⟨3612744892994170830037901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408496595329447220025267 3612744892994170830037901)
      ·
        refine ⟨1354779334872814061264213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3612744892994170830037901 1354779334872814061264213)
        ·
          refine ⟨1984540041317598722555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1354779334872814061264213 1984540041317598722555)
          ·
            rfl

theorem cell21_704374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 11].length) (baseStart_704374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704374 prefixEnd_704374 := by exact prefixLift 704374
  have htrace : WordTrace (prefixWord ++ tailWord_704374) baseStart_704374 baseEnd_704374 := by
    simpa [prefixWord, tailWord_704374, baseEnd_704374] using wordTrace_append hprefix tailTrace_704374
  have hstable : (prefixWord ++ tailWord_704374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704374).length < 2 ^ (prefixWord ++ tailWord_704374).sum := by decide
  have hdescent : baseEnd_704374 < baseStart_704374 := by decide
  rcases family_descends (prefixWord ++ tailWord_704374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704391 : List Nat := [1, 1, 4, 2, 4, 2, 1, 6]
def baseStart_704391 : Nat := 118140960795 + 704391 * 2 ^ 59
def prefixEnd_704391 : Nat := 4983230072969 + 3 ^ 40 * 704391 * 2
def baseEnd_704391 : Nat := 53583874326112414914529

theorem tailTrace_704391 : CollatzResearch.WordTrace tailWord_704391 prefixEnd_704391 53583874326112414914529 := by
  unfold tailWord_704391
  simp only [CollatzResearch.WordTrace]
  refine ⟨25691250391119182250305027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17127500260746121500203351 25691250391119182250305027)
  ·
    refine ⟨38536875586678773375457541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25691250391119182250305027 38536875586678773375457541)
    ·
      refine ⟨7225664172502270007898289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38536875586678773375457541 7225664172502270007898289)
      ·
        refine ⟨5419248129376702505923717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7225664172502270007898289 5419248129376702505923717)
        ·
          refine ⟨1016109024258131719860697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5419248129376702505923717 1016109024258131719860697)
          ·
            refine ⟨762081768193598789895523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1016109024258131719860697 762081768193598789895523)
            ·
              refine ⟨1143122652290398184843285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762081768193598789895523 1143122652290398184843285)
              ·
                refine ⟨53583874326112414914529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1143122652290398184843285 53583874326112414914529)
                ·
                  rfl

theorem cell21_704391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 6].length) (baseStart_704391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704391 prefixEnd_704391 := by exact prefixLift 704391
  have htrace : WordTrace (prefixWord ++ tailWord_704391) baseStart_704391 baseEnd_704391 := by
    simpa [prefixWord, tailWord_704391, baseEnd_704391] using wordTrace_append hprefix tailTrace_704391
  have hstable : (prefixWord ++ tailWord_704391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704391).length < 2 ^ (prefixWord ++ tailWord_704391).sum := by decide
  have hdescent : baseEnd_704391 < baseStart_704391 := by decide
  rcases family_descends (prefixWord ++ tailWord_704391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704408 : List Nat := [2, 1, 2, 6, 1, 1, 3, 5]
def baseStart_704408 : Nat := 118140960795 + 704408 * 2 ^ 59
def prefixEnd_704408 : Nat := 4983230072969 + 3 ^ 40 * 704408 * 2
def baseEnd_704408 : Nat := 53585167536649664320073

theorem tailTrace_704408 : CollatzResearch.WordTrace tailWord_704408 prefixEnd_704408 53585167536649664320073 := by
  unfold tailWord_704408
  simp only [CollatzResearch.WordTrace]
  refine ⟨12845935216028797076836939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17127913621371729435782585 12845935216028797076836939)
  ·
    refine ⟨19268902824043195615255409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12845935216028797076836939 19268902824043195615255409)
    ·
      refine ⟨14451677118032396711441557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19268902824043195615255409 14451677118032396711441557)
      ·
        refine ⟨677422364907768595848823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14451677118032396711441557 677422364907768595848823)
        ·
          refine ⟨1016133547361652893773235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677422364907768595848823 1016133547361652893773235)
          ·
            refine ⟨1524200321042479340659853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016133547361652893773235 1524200321042479340659853)
            ·
              refine ⟨571575120390929752747445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1524200321042479340659853 571575120390929752747445)
              ·
                refine ⟨53585167536649664320073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 571575120390929752747445 53585167536649664320073)
                ·
                  rfl

theorem cell21_704408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_704408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704408 prefixEnd_704408 := by exact prefixLift 704408
  have htrace : WordTrace (prefixWord ++ tailWord_704408) baseStart_704408 baseEnd_704408 := by
    simpa [prefixWord, tailWord_704408, baseEnd_704408] using wordTrace_append hprefix tailTrace_704408
  have hstable : (prefixWord ++ tailWord_704408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704408).length < 2 ^ (prefixWord ++ tailWord_704408).sum := by decide
  have hdescent : baseEnd_704408 < baseStart_704408 := by decide
  rcases family_descends (prefixWord ++ tailWord_704408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704464 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_704464 : Nat := 118140960795 + 704464 * 2 ^ 59
def prefixEnd_704464 : Nat := 4983230072969 + 3 ^ 40 * 704464 * 2
def baseEnd_704464 : Nat := 160768282572905340026771

theorem tailTrace_704464 : CollatzResearch.WordTrace tailWord_704464 prefixEnd_704464 160768282572905340026771 := by
  unfold tailWord_704464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12846956459927357858856223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17129275279903143811808297 12846956459927357858856223)
  ·
    refine ⟨19270434689891036788284335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12846956459927357858856223 19270434689891036788284335)
    ·
      refine ⟨28905652034836555182426503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19270434689891036788284335 28905652034836555182426503)
      ·
        refine ⟨43358478052254832773639755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28905652034836555182426503 43358478052254832773639755)
        ·
          refine ⟨65037717078382249160459633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43358478052254832773639755 65037717078382249160459633)
          ·
            refine ⟨48778287808786686870344725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65037717078382249160459633 48778287808786686870344725)
            ·
              refine ⟨2286482241036875947047409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48778287808786686870344725 2286482241036875947047409)
              ·
                refine ⟨1714861680777656960285557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286482241036875947047409 1714861680777656960285557)
                ·
                  refine ⟨160768282572905340026771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1714861680777656960285557 160768282572905340026771)
                  ·
                    rfl

theorem cell21_704464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_704464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704464 prefixEnd_704464 := by exact prefixLift 704464
  have htrace : WordTrace (prefixWord ++ tailWord_704464) baseStart_704464 baseEnd_704464 := by
    simpa [prefixWord, tailWord_704464, baseEnd_704464] using wordTrace_append hprefix tailTrace_704464
  have hstable : (prefixWord ++ tailWord_704464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704464).length < 2 ^ (prefixWord ++ tailWord_704464).sum := by decide
  have hdescent : baseEnd_704464 < baseStart_704464 := by decide
  rcases family_descends (prefixWord ++ tailWord_704464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704495 : List Nat := [1, 1, 2, 1, 4, 2, 2, 4, 4]
def baseStart_704495 : Nat := 118140960795 + 704495 * 2 ^ 59
def prefixEnd_704495 : Nat := 4983230072969 + 3 ^ 40 * 704495 * 2
def baseEnd_704495 : Nat := 160775357195256175010041

theorem tailTrace_704495 : CollatzResearch.WordTrace tailWord_704495 prefixEnd_704495 160775357195256175010041 := by
  unfold tailWord_704495
  simp only [CollatzResearch.WordTrace]
  refine ⟨25695043582742408012090939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17130029055161605341393959 25695043582742408012090939)
  ·
    refine ⟨38542565374113612018136409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25695043582742408012090939 38542565374113612018136409)
    ·
      refine ⟨28906924030585209013602307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38542565374113612018136409 28906924030585209013602307)
      ·
        refine ⟨43360386045877813520403461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28906924030585209013602307 43360386045877813520403461)
        ·
          refine ⟨8130072383602090035075649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43360386045877813520403461 8130072383602090035075649)
          ·
            refine ⟨6097554287701567526306737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8130072383602090035075649 6097554287701567526306737)
            ·
              refine ⟨4573165715776175644730053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6097554287701567526306737 4573165715776175644730053)
              ·
                refine ⟨857468571708032933386885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4573165715776175644730053 857468571708032933386885)
                ·
                  refine ⟨160775357195256175010041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857468571708032933386885 160775357195256175010041)
                  ·
                    rfl

theorem cell21_704495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 4].length) (baseStart_704495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704495 prefixEnd_704495 := by exact prefixLift 704495
  have htrace : WordTrace (prefixWord ++ tailWord_704495) baseStart_704495 baseEnd_704495 := by
    simpa [prefixWord, tailWord_704495, baseEnd_704495] using wordTrace_append hprefix tailTrace_704495
  have hstable : (prefixWord ++ tailWord_704495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704495).length < 2 ^ (prefixWord ++ tailWord_704495).sum := by decide
  have hdescent : baseEnd_704495 < baseStart_704495 := by decide
  rcases family_descends (prefixWord ++ tailWord_704495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704509 : List Nat := [1, 4, 1, 1, 1, 2, 3, 8]
def baseStart_704509 : Nat := 118140960795 + 704509 * 2 ^ 59
def prefixEnd_704509 : Nat := 4983230072969 + 3 ^ 40 * 704509 * 2
def baseEnd_704509 : Nat := 53592850728665087258893

theorem tailTrace_704509 : CollatzResearch.WordTrace tailWord_704509 prefixEnd_704509 53592850728665087258893 := by
  unfold tailWord_704509
  simp only [CollatzResearch.WordTrace]
  refine ⟨25695554204691688403100581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17130369469794458935400387 25695554204691688403100581)
  ·
    refine ⟨4817916413379691575581359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25695554204691688403100581 4817916413379691575581359)
    ·
      refine ⟨7226874620069537363372039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4817916413379691575581359 7226874620069537363372039)
      ·
        refine ⟨10840311930104306045058059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7226874620069537363372039 10840311930104306045058059)
        ·
          refine ⟨16260467895156459067587089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10840311930104306045058059 16260467895156459067587089)
          ·
            refine ⟨12195350921367344300690317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16260467895156459067587089 12195350921367344300690317)
            ·
              refine ⟨4573256595512754112758869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12195350921367344300690317 4573256595512754112758869)
              ·
                refine ⟨53592850728665087258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4573256595512754112758869 53592850728665087258893)
                ·
                  rfl

theorem cell21_704509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 8].length) (baseStart_704509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704509 prefixEnd_704509 := by exact prefixLift 704509
  have htrace : WordTrace (prefixWord ++ tailWord_704509) baseStart_704509 baseEnd_704509 := by
    simpa [prefixWord, tailWord_704509, baseEnd_704509] using wordTrace_append hprefix tailTrace_704509
  have hstable : (prefixWord ++ tailWord_704509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704509).length < 2 ^ (prefixWord ++ tailWord_704509).sum := by decide
  have hdescent : baseEnd_704509 < baseStart_704509 := by decide
  rcases family_descends (prefixWord ++ tailWord_704509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704574 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_704574 : Nat := 118140960795 + 704574 * 2 ^ 59
def prefixEnd_704574 : Nat := 4983230072969 + 3 ^ 40 * 704574 * 2
def baseEnd_704574 : Nat := 160793386071569593193213

theorem tailTrace_704574 : CollatzResearch.WordTrace tailWord_704574 prefixEnd_704574 160793386071569593193213 := by
  unfold tailWord_704574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212240618682025563027097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17131949966304136336144517 3212240618682025563027097)
  ·
    refine ⟨2409180464011519172270323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3212240618682025563027097 2409180464011519172270323)
    ·
      refine ⟨3613770696017278758405485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2409180464011519172270323 3613770696017278758405485)
      ·
        refine ⟨1355164011006479534402057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3613770696017278758405485 1355164011006479534402057)
        ·
          refine ⟨1016373008254859650801543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355164011006479534402057 1016373008254859650801543)
          ·
            refine ⟨1524559512382289476202315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016373008254859650801543 1524559512382289476202315)
            ·
              refine ⟨2286839268573434214303473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524559512382289476202315 2286839268573434214303473)
              ·
                refine ⟨1715129451430075660727605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286839268573434214303473 1715129451430075660727605)
                ·
                  refine ⟨160793386071569593193213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1715129451430075660727605 160793386071569593193213)
                  ·
                    rfl

theorem cell21_704574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_704574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704574 prefixEnd_704574 := by exact prefixLift 704574
  have htrace : WordTrace (prefixWord ++ tailWord_704574) baseStart_704574 baseEnd_704574 := by
    simpa [prefixWord, tailWord_704574, baseEnd_704574] using wordTrace_append hprefix tailTrace_704574
  have hstable : (prefixWord ++ tailWord_704574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704574).length < 2 ^ (prefixWord ++ tailWord_704574).sum := by decide
  have hdescent : baseEnd_704574 < baseStart_704574 := by decide
  rcases family_descends (prefixWord ++ tailWord_704574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704605 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 4]
def baseStart_704605 : Nat := 118140960795 + 704605 * 2 ^ 59
def prefixEnd_704605 : Nat := 4983230072969 + 3 ^ 40 * 704605 * 2
def baseEnd_704605 : Nat := 160800460693920428176483

theorem tailTrace_704605 : CollatzResearch.WordTrace tailWord_704605 prefixEnd_704605 160800460693920428176483 := by
  unfold tailWord_704605
  simp only [CollatzResearch.WordTrace]
  refine ⟨25699055612343896798595269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17132703741562597865730179 25699055612343896798595269)
  ·
    refine ⟨4818572927314480649736613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25699055612343896798595269 4818572927314480649736613)
    ·
      refine ⟨903482423871465121825615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4818572927314480649736613 903482423871465121825615)
      ·
        refine ⟨1355223635807197682738423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903482423871465121825615 1355223635807197682738423)
        ·
          refine ⟨2032835453710796524107635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355223635807197682738423 2032835453710796524107635)
          ·
            refine ⟨3049253180566194786161453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032835453710796524107635 3049253180566194786161453)
            ·
              refine ⟨1143469942712323044810545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3049253180566194786161453 1143469942712323044810545)
              ·
                refine ⟨857602457034242283607909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1143469942712323044810545 857602457034242283607909)
                ·
                  refine ⟨160800460693920428176483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 857602457034242283607909 160800460693920428176483)
                  ·
                    rfl

theorem cell21_704605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_704605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704605 prefixEnd_704605 := by exact prefixLift 704605
  have htrace : WordTrace (prefixWord ++ tailWord_704605) baseStart_704605 baseEnd_704605 := by
    simpa [prefixWord, tailWord_704605, baseEnd_704605] using wordTrace_append hprefix tailTrace_704605
  have hstable : (prefixWord ++ tailWord_704605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704605).length < 2 ^ (prefixWord ++ tailWord_704605).sum := by decide
  have hdescent : baseEnd_704605 < baseStart_704605 := by decide
  rcases family_descends (prefixWord ++ tailWord_704605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704650 : List Nat := [3, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_704650 : Nat := 118140960795 + 704650 * 2 ^ 59
def prefixEnd_704650 : Nat := 4983230072969 + 3 ^ 40 * 704650 * 2
def baseEnd_704650 : Nat := 160810730307010349926391

theorem tailTrace_704650 : CollatzResearch.WordTrace tailWord_704650 prefixEnd_704650 160810730307010349926391 := by
  unfold tailWord_704650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6425174224295217370995851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17133797931453912989322269 6425174224295217370995851)
  ·
    refine ⟨9637761336442826056493777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6425174224295217370995851 9637761336442826056493777)
    ·
      refine ⟨7228321002332119542370333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9637761336442826056493777 7228321002332119542370333)
      ·
        refine ⟨2710620375874544828388875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7228321002332119542370333 2710620375874544828388875)
        ·
          refine ⟨4065930563811817242583313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2710620375874544828388875 4065930563811817242583313)
          ·
            refine ⟨3049447922858862931937485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4065930563811817242583313 3049447922858862931937485)
            ·
              refine ⟨1143542971072073599476557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3049447922858862931937485 1143542971072073599476557)
              ·
                refine ⟨428828614152027599803709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1143542971072073599476557 428828614152027599803709)
                ·
                  refine ⟨160810730307010349926391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428828614152027599803709 160810730307010349926391)
                  ·
                    rfl

theorem cell21_704650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_704650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704650 prefixEnd_704650 := by exact prefixLift 704650
  have htrace : WordTrace (prefixWord ++ tailWord_704650) baseStart_704650 baseEnd_704650 := by
    simpa [prefixWord, tailWord_704650, baseEnd_704650] using wordTrace_append hprefix tailTrace_704650
  have hstable : (prefixWord ++ tailWord_704650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704650).length < 2 ^ (prefixWord ++ tailWord_704650).sum := by decide
  have hdescent : baseEnd_704650 < baseStart_704650 := by decide
  rcases family_descends (prefixWord ++ tailWord_704650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704785 : List Nat := [1, 2, 2, 1, 1, 5, 2, 4, 3]
def baseStart_704785 : Nat := 118140960795 + 704785 * 2 ^ 59
def prefixEnd_704785 : Nat := 4983230072969 + 3 ^ 40 * 704785 * 2
def baseEnd_704785 : Nat := 160841539146280115176115

theorem tailTrace_704785 : CollatzResearch.WordTrace tailWord_704785 prefixEnd_704785 160841539146280115176115 := by
  unfold tailWord_704785
  simp only [CollatzResearch.WordTrace]
  refine ⟨25705620751691787540147809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17137080501127858360098539 25705620751691787540147809)
  ·
    refine ⟨19279215563768840655110857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25705620751691787540147809 19279215563768840655110857)
    ·
      refine ⟨14459411672826630491333143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19279215563768840655110857 14459411672826630491333143)
      ·
        refine ⟨21689117509239945736999715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14459411672826630491333143 21689117509239945736999715)
        ·
          refine ⟨32533676263859918605499573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21689117509239945736999715 32533676263859918605499573)
          ·
            refine ⟨3050032149736867369265585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32533676263859918605499573 3050032149736867369265585)
            ·
              refine ⟨2287524112302650526949189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3050032149736867369265585 2287524112302650526949189)
              ·
                refine ⟨428910771056746973802973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2287524112302650526949189 428910771056746973802973)
                ·
                  refine ⟨160841539146280115176115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428910771056746973802973 160841539146280115176115)
                  ·
                    rfl

theorem cell21_704785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_704785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704785 prefixEnd_704785 := by exact prefixLift 704785
  have htrace : WordTrace (prefixWord ++ tailWord_704785) baseStart_704785 baseEnd_704785 := by
    simpa [prefixWord, tailWord_704785, baseEnd_704785] using wordTrace_append hprefix tailTrace_704785
  have hstable : (prefixWord ++ tailWord_704785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704785).length < 2 ^ (prefixWord ++ tailWord_704785).sum := by decide
  have hdescent : baseEnd_704785 < baseStart_704785 := by decide
  rcases family_descends (prefixWord ++ tailWord_704785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704830 : List Nat := [4, 2, 1, 2, 1, 4, 7]
def baseStart_704830 : Nat := 118140960795 + 704830 * 2 ^ 59
def prefixEnd_704830 : Nat := 4983230072969 + 3 ^ 40 * 704830 * 2
def baseEnd_704830 : Nat := 17872423195485559658447

theorem tailTrace_704830 : CollatzResearch.WordTrace tailWord_704830 prefixEnd_704830 17872423195485559658447 := by
  unfold tailWord_704830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213407754566095028191993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17138174691019173483690629 3213407754566095028191993)
  ·
    refine ⟨2410055815924571271143995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3213407754566095028191993 2410055815924571271143995)
    ·
      refine ⟨3615083723886856906715993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410055815924571271143995 3615083723886856906715993)
      ·
        refine ⟨2711312792915142680036995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3615083723886856906715993 2711312792915142680036995)
        ·
          refine ⟨4066969189372714020055493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711312792915142680036995 4066969189372714020055493)
          ·
            refine ⟨762556723007383878760405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4066969189372714020055493 762556723007383878760405)
            ·
              refine ⟨17872423195485559658447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 762556723007383878760405 17872423195485559658447)
              ·
                rfl

theorem cell21_704830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 7].length) (baseStart_704830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704830 prefixEnd_704830 := by exact prefixLift 704830
  have htrace : WordTrace (prefixWord ++ tailWord_704830) baseStart_704830 baseEnd_704830 := by
    simpa [prefixWord, tailWord_704830, baseEnd_704830] using wordTrace_append hprefix tailTrace_704830
  have hstable : (prefixWord ++ tailWord_704830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704830).length < 2 ^ (prefixWord ++ tailWord_704830).sum := by decide
  have hdescent : baseEnd_704830 < baseStart_704830 := by decide
  rcases family_descends (prefixWord ++ tailWord_704830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704836 : List Nat := [2, 3, 4, 1, 2, 1, 3, 2, 3]
def baseStart_704836 : Nat := 118140960795 + 704836 * 2 ^ 59
def prefixEnd_704836 : Nat := 4983230072969 + 3 ^ 40 * 704836 * 2
def baseEnd_704836 : Nat := 160853178041115359826011

theorem tailTrace_704836 : CollatzResearch.WordTrace tailWord_704836 prefixEnd_704836 160853178041115359826011 := by
  unfold tailWord_704836
  simp only [CollatzResearch.WordTrace]
  refine ⟨12853740437253511625127181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17138320583004682166836241 12853740437253511625127181)
  ·
    refine ⟨4820152663970066859422693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12853740437253511625127181 4820152663970066859422693)
    ·
      refine ⟨903778624494387536141755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4820152663970066859422693 903778624494387536141755)
      ·
        refine ⟨1355667936741581304212633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903778624494387536141755 1355667936741581304212633)
        ·
          refine ⟨1016750952556185978159475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355667936741581304212633 1016750952556185978159475)
          ·
            refine ⟨1525126428834278967239213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016750952556185978159475 1525126428834278967239213)
            ·
              refine ⟨571922410812854612714705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1525126428834278967239213 571922410812854612714705)
              ·
                refine ⟨428941808109640959536029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571922410812854612714705 428941808109640959536029)
                ·
                  refine ⟨160853178041115359826011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428941808109640959536029 160853178041115359826011)
                  ·
                    rfl

theorem cell21_704836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_704836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704836 prefixEnd_704836 := by exact prefixLift 704836
  have htrace : WordTrace (prefixWord ++ tailWord_704836) baseStart_704836 baseEnd_704836 := by
    simpa [prefixWord, tailWord_704836, baseEnd_704836] using wordTrace_append hprefix tailTrace_704836
  have hstable : (prefixWord ++ tailWord_704836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704836).length < 2 ^ (prefixWord ++ tailWord_704836).sum := by decide
  have hdescent : baseEnd_704836 < baseStart_704836 := by decide
  rcases family_descends (prefixWord ++ tailWord_704836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704920 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_704920 : Nat := 118140960795 + 704920 * 2 ^ 59
def prefixEnd_704920 : Nat := 4983230072969 + 3 ^ 40 * 704920 * 2
def baseEnd_704920 : Nat := 160872347985549880425839

theorem tailTrace_704920 : CollatzResearch.WordTrace tailWord_704920 prefixEnd_704920 160872347985549880425839 := by
  unfold tailWord_704920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12855272303101352798156107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17140363070801803730874809 12855272303101352798156107)
  ·
    refine ⟨19282908454652029197234161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12855272303101352798156107 19282908454652029197234161)
    ·
      refine ⟨14462181340989021897925621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19282908454652029197234161 14462181340989021897925621)
      ·
        refine ⟨1355829500717720802930527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14462181340989021897925621 1355829500717720802930527)
        ·
          refine ⟨2033744251076581204395791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1355829500717720802930527 2033744251076581204395791)
          ·
            refine ⟨3050616376614871806593687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033744251076581204395791 3050616376614871806593687)
            ·
              refine ⟨4575924564922307709890531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3050616376614871806593687 4575924564922307709890531)
              ·
                refine ⟨6863886847383461564835797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4575924564922307709890531 6863886847383461564835797)
                ·
                  refine ⟨160872347985549880425839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6863886847383461564835797 160872347985549880425839)
                  ·
                    rfl

theorem cell21_704920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_704920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704920 prefixEnd_704920 := by exact prefixLift 704920
  have htrace : WordTrace (prefixWord ++ tailWord_704920) baseStart_704920 baseEnd_704920 := by
    simpa [prefixWord, tailWord_704920, baseEnd_704920] using wordTrace_append hprefix tailTrace_704920
  have hstable : (prefixWord ++ tailWord_704920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704920).length < 2 ^ (prefixWord ++ tailWord_704920).sum := by decide
  have hdescent : baseEnd_704920 < baseStart_704920 := by decide
  rcases family_descends (prefixWord ++ tailWord_704920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704951 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 4]
def baseStart_704951 : Nat := 118140960795 + 704951 * 2 ^ 59
def prefixEnd_704951 : Nat := 4983230072969 + 3 ^ 40 * 704951 * 2
def baseEnd_704951 : Nat := 160879422607900715409109

theorem tailTrace_704951 : CollatzResearch.WordTrace tailWord_704951 prefixEnd_704951 160879422607900715409109 := by
  unfold tailWord_704951
  simp only [CollatzResearch.WordTrace]
  refine ⟨25711675269090397890690707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17141116846060265260460471 25711675269090397890690707)
  ·
    refine ⟨38567512903635596836036061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25711675269090397890690707 38567512903635596836036061)
    ·
      refine ⟨14462817338863348813513523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38567512903635596836036061 14462817338863348813513523)
      ·
        refine ⟨21694226008295023220270285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14462817338863348813513523 21694226008295023220270285)
        ·
          refine ⟨8135334753110633707601357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21694226008295023220270285 8135334753110633707601357)
          ·
            refine ⟨3050750532416487640350509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8135334753110633707601357 3050750532416487640350509)
            ·
              refine ⟨1144031449656182865131441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3050750532416487640350509 1144031449656182865131441)
              ·
                refine ⟨858023587242137148848581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144031449656182865131441 858023587242137148848581)
                ·
                  refine ⟨160879422607900715409109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858023587242137148848581 160879422607900715409109)
                  ·
                    rfl

theorem cell21_704951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 4].length) (baseStart_704951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704951 prefixEnd_704951 := by exact prefixLift 704951
  have htrace : WordTrace (prefixWord ++ tailWord_704951) baseStart_704951 baseEnd_704951 := by
    simpa [prefixWord, tailWord_704951, baseEnd_704951] using wordTrace_append hprefix tailTrace_704951
  have hstable : (prefixWord ++ tailWord_704951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704951).length < 2 ^ (prefixWord ++ tailWord_704951).sum := by decide
  have hdescent : baseEnd_704951 < baseStart_704951 := by decide
  rcases family_descends (prefixWord ++ tailWord_704951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704968 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_704968 : Nat := 118140960795 + 704968 * 2 ^ 59
def prefixEnd_704968 : Nat := 4983230072969 + 3 ^ 40 * 704968 * 2
def baseEnd_704968 : Nat := 160883302239512463625741

theorem tailTrace_704968 : CollatzResearch.WordTrace tailWord_704968 prefixEnd_704968 160883302239512463625741 := by
  unfold tailWord_704968
  simp only [CollatzResearch.WordTrace]
  refine ⟨12856147655014404897029779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17141530206685873196039705 12856147655014404897029779)
  ·
    refine ⟨19284221482521607345544669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12856147655014404897029779 19284221482521607345544669)
    ·
      refine ⟨7231583055945602754579251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19284221482521607345544669 7231583055945602754579251)
      ·
        refine ⟨10847374583918404131868877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7231583055945602754579251 10847374583918404131868877)
        ·
          refine ⟨4067765468969401549450829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10847374583918404131868877 4067765468969401549450829)
          ·
            refine ⟨1525412050863525581044061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4067765468969401549450829 1525412050863525581044061)
            ·
              refine ⟨572029519073822092891523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1525412050863525581044061 572029519073822092891523)
              ·
                refine ⟨858044278610733139337285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572029519073822092891523 858044278610733139337285)
                ·
                  refine ⟨160883302239512463625741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858044278610733139337285 160883302239512463625741)
                  ·
                    rfl

theorem cell21_704968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_704968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704968 prefixEnd_704968 := by exact prefixLift 704968
  have htrace : WordTrace (prefixWord ++ tailWord_704968) baseStart_704968 baseEnd_704968 := by
    simpa [prefixWord, tailWord_704968, baseEnd_704968] using wordTrace_append hprefix tailTrace_704968
  have hstable : (prefixWord ++ tailWord_704968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704968).length < 2 ^ (prefixWord ++ tailWord_704968).sum := by decide
  have hdescent : baseEnd_704968 < baseStart_704968 := by decide
  rcases family_descends (prefixWord ++ tailWord_704968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_704982 : List Nat := [5, 2, 1, 1, 1, 1, 3, 7]
def baseStart_704982 : Nat := 118140960795 + 704982 * 2 ^ 59
def prefixEnd_704982 : Nat := 4983230072969 + 3 ^ 40 * 704982 * 2
def baseEnd_704982 : Nat := 53628832410083850130793

theorem tailTrace_704982 : CollatzResearch.WordTrace tailWord_704982 prefixEnd_704982 53628832410083850130793 := by
  unfold tailWord_704982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1607050370748630636566825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17141870621318726790046133 1607050370748630636566825)
  ·
    refine ⟨1205287778061472977425119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1607050370748630636566825 1205287778061472977425119)
    ·
      refine ⟨1807931667092209466137679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205287778061472977425119 1807931667092209466137679)
      ·
        refine ⟨2711897500638314199206519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1807931667092209466137679 2711897500638314199206519)
        ·
          refine ⟨4067846250957471298809779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2711897500638314199206519 4067846250957471298809779)
          ·
            refine ⟨6101769376436206948214669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067846250957471298809779 6101769376436206948214669)
            ·
              refine ⟨2288163516163577605580501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6101769376436206948214669 2288163516163577605580501)
              ·
                refine ⟨53628832410083850130793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2288163516163577605580501 53628832410083850130793)
                ·
                  rfl

theorem cell21_704982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_704982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_704982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_704982 prefixEnd_704982 := by exact prefixLift 704982
  have htrace : WordTrace (prefixWord ++ tailWord_704982) baseStart_704982 baseEnd_704982 := by
    simpa [prefixWord, tailWord_704982, baseEnd_704982] using wordTrace_append hprefix tailTrace_704982
  have hstable : (prefixWord ++ tailWord_704982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_704982).length < 2 ^ (prefixWord ++ tailWord_704982).sum := by decide
  have hdescent : baseEnd_704982 < baseStart_704982 := by decide
  rcases family_descends (prefixWord ++ tailWord_704982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705449 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 6]
def baseStart_705449 : Nat := 118140960795 + 705449 * 2 ^ 59
def prefixEnd_705449 : Nat := 4983230072969 + 3 ^ 40 * 705449 * 2
def baseEnd_705449 : Nat := 160993072992762516108091

theorem tailTrace_705449 : CollatzResearch.WordTrace tailWord_705449 prefixEnd_705449 160993072992762516108091 := by
  unfold tailWord_705449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25729838821286228942319401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17153225880857485961546267 25729838821286228942319401)
  ·
    refine ⟨19297379115964671706739551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25729838821286228942319401 19297379115964671706739551)
    ·
      refine ⟨28946068673947007560109327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19297379115964671706739551 28946068673947007560109327)
      ·
        refine ⟨43419103010920511340163991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28946068673947007560109327 43419103010920511340163991)
        ·
          refine ⟨65128654516380767010245987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43419103010920511340163991 65128654516380767010245987)
          ·
            refine ⟨97692981774571150515368981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65128654516380767010245987 97692981774571150515368981)
            ·
              refine ⟨4579358520683022680407921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97692981774571150515368981 4579358520683022680407921)
              ·
                refine ⟨3434518890512267010305941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4579358520683022680407921 3434518890512267010305941)
                ·
                  refine ⟨160993072992762516108091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3434518890512267010305941 160993072992762516108091)
                  ·
                    rfl

theorem cell21_705449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_705449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705449 prefixEnd_705449 := by exact prefixLift 705449
  have htrace : WordTrace (prefixWord ++ tailWord_705449) baseStart_705449 baseEnd_705449 := by
    simpa [prefixWord, tailWord_705449, baseEnd_705449] using wordTrace_append hprefix tailTrace_705449
  have hstable : (prefixWord ++ tailWord_705449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705449).length < 2 ^ (prefixWord ++ tailWord_705449).sum := by decide
  have hdescent : baseEnd_705449 < baseStart_705449 := by decide
  rcases family_descends (prefixWord ++ tailWord_705449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705483 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 4]
def baseStart_705483 : Nat := 118140960795 + 705483 * 2 ^ 59
def prefixEnd_705483 : Nat := 4983230072969 + 3 ^ 40 * 705483 * 2
def baseEnd_705483 : Nat := 161000832255986012541355

theorem tailTrace_705483 : CollatzResearch.WordTrace tailWord_705483 prefixEnd_705483 161000832255986012541355 := by
  unfold tailWord_705483
  simp only [CollatzResearch.WordTrace]
  refine ⟨25731078903163052749057103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17154052602108701832704735 25731078903163052749057103)
  ·
    refine ⟨38596618354744579123585655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25731078903163052749057103 38596618354744579123585655)
    ·
      refine ⟨57894927532116868685378483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38596618354744579123585655 57894927532116868685378483)
      ·
        refine ⟨86842391298175303028067725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57894927532116868685378483 86842391298175303028067725)
        ·
          refine ⟨32565896736815738635525397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86842391298175303028067725 32565896736815738635525397)
          ·
            refine ⟨1526526409538237748540253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32565896736815738635525397 1526526409538237748540253)
            ·
              refine ⟨572447403576839155702595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1526526409538237748540253 572447403576839155702595)
              ·
                refine ⟨858671105365258733553893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572447403576839155702595 858671105365258733553893)
                ·
                  refine ⟨161000832255986012541355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858671105365258733553893 161000832255986012541355)
                  ·
                    rfl

theorem cell21_705483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 4].length) (baseStart_705483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705483 prefixEnd_705483 := by exact prefixLift 705483
  have htrace : WordTrace (prefixWord ++ tailWord_705483) baseStart_705483 baseEnd_705483 := by
    simpa [prefixWord, tailWord_705483, baseEnd_705483] using wordTrace_append hprefix tailTrace_705483
  have hstable : (prefixWord ++ tailWord_705483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705483).length < 2 ^ (prefixWord ++ tailWord_705483).sum := by decide
  have hdescent : baseEnd_705483 < baseStart_705483 := by decide
  rcases family_descends (prefixWord ++ tailWord_705483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705497 : List Nat := [1, 2, 1, 2, 5, 1, 4, 5]
def baseStart_705497 : Nat := 118140960795 + 705497 * 2 ^ 59
def prefixEnd_705497 : Nat := 4983230072969 + 3 ^ 40 * 705497 * 2
def baseEnd_705497 : Nat := 53668009082241699769331

theorem tailTrace_705497 : CollatzResearch.WordTrace tailWord_705497 prefixEnd_705497 53668009082241699769331 := by
  unfold tailWord_705497
  simp only [CollatzResearch.WordTrace]
  refine ⟨25731589525112333140066745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17154393016741555426711163 25731589525112333140066745)
  ·
    refine ⟨19298692143834249855050059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25731589525112333140066745 19298692143834249855050059)
    ·
      refine ⟨28948038215751374782575089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19298692143834249855050059 28948038215751374782575089)
      ·
        refine ⟨21711028661813531086931317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28948038215751374782575089 21711028661813531086931317)
        ·
          refine ⟨2035408937045018539399811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21711028661813531086931317 2035408937045018539399811)
          ·
            refine ⟨3053113405567527809099717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035408937045018539399811 3053113405567527809099717)
            ·
              refine ⟨572458763543911464206197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3053113405567527809099717 572458763543911464206197)
              ·
                refine ⟨53668009082241699769331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 572458763543911464206197 53668009082241699769331)
                ·
                  rfl

theorem cell21_705497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 5].length) (baseStart_705497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705497 prefixEnd_705497 := by exact prefixLift 705497
  have htrace : WordTrace (prefixWord ++ tailWord_705497) baseStart_705497 baseEnd_705497 := by
    simpa [prefixWord, tailWord_705497, baseEnd_705497] using wordTrace_append hprefix tailTrace_705497
  have hstable : (prefixWord ++ tailWord_705497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705497).length < 2 ^ (prefixWord ++ tailWord_705497).sum := by decide
  have hdescent : baseEnd_705497 < baseStart_705497 := by decide
  rcases family_descends (prefixWord ++ tailWord_705497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705534 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_705534 : Nat := 118140960795 + 705534 * 2 ^ 59
def prefixEnd_705534 : Nat := 4983230072969 + 3 ^ 40 * 705534 * 2
def baseEnd_705534 : Nat := 161012471150821257191251

theorem tailTrace_705534 : CollatzResearch.WordTrace tailWord_705534 prefixEnd_705534 161012471150821257191251 := by
  unfold tailWord_705534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216617378247286057395457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17155292683985525639442437 3216617378247286057395457)
  ·
    refine ⟨2412463033685464543046593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3216617378247286057395457 2412463033685464543046593)
    ·
      refine ⟨1809347275264098407284945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2412463033685464543046593 1809347275264098407284945)
      ·
        refine ⟨1357010456448073805463709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1809347275264098407284945 1357010456448073805463709)
        ·
          refine ⟨508878921168027677048891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1357010456448073805463709 508878921168027677048891)
          ·
            refine ⟨763318381752041515573337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508878921168027677048891 763318381752041515573337)
            ·
              refine ⟨572488786314031136680003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763318381752041515573337 572488786314031136680003)
              ·
                refine ⟨858733179471046705020005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572488786314031136680003 858733179471046705020005)
                ·
                  refine ⟨161012471150821257191251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858733179471046705020005 161012471150821257191251)
                  ·
                    rfl

theorem cell21_705534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_705534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705534 prefixEnd_705534 := by exact prefixLift 705534
  have htrace : WordTrace (prefixWord ++ tailWord_705534) baseStart_705534 baseEnd_705534 := by
    simpa [prefixWord, tailWord_705534, baseEnd_705534] using wordTrace_append hprefix tailTrace_705534
  have hstable : (prefixWord ++ tailWord_705534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705534).length < 2 ^ (prefixWord ++ tailWord_705534).sum := by decide
  have hdescent : baseEnd_705534 < baseStart_705534 := by decide
  rcases family_descends (prefixWord ++ tailWord_705534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705590 : List Nat := [5, 1, 2, 1, 1, 4, 1, 6]
def baseStart_705590 : Nat := 118140960795 + 705590 * 2 ^ 59
def prefixEnd_705590 : Nat := 4983230072969 + 3 ^ 40 * 705590 * 2
def baseEnd_705590 : Nat := 53675083704592534752601

theorem tailTrace_705590 : CollatzResearch.WordTrace tailWord_705590 prefixEnd_705590 53675083704592534752601 := by
  unfold tailWord_705590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608436344610963126450139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17156654342516940015468149 1608436344610963126450139)
  ·
    refine ⟨2412654516916444689675209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1608436344610963126450139 2412654516916444689675209)
    ·
      refine ⟨1809490887687333517256407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2412654516916444689675209 1809490887687333517256407)
      ·
        refine ⟨2714236331531000275884611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809490887687333517256407 2714236331531000275884611)
        ·
          refine ⟨4071354497296500413826917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714236331531000275884611 4071354497296500413826917)
          ·
            refine ⟨763378968243093827592547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4071354497296500413826917 763378968243093827592547)
            ·
              refine ⟨1145068452364640741388821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763378968243093827592547 1145068452364640741388821)
              ·
                refine ⟨53675083704592534752601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1145068452364640741388821 53675083704592534752601)
                ·
                  rfl

theorem cell21_705590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_705590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705590 prefixEnd_705590 := by exact prefixLift 705590
  have htrace : WordTrace (prefixWord ++ tailWord_705590) baseStart_705590 baseEnd_705590 := by
    simpa [prefixWord, tailWord_705590, baseEnd_705590] using wordTrace_append hprefix tailTrace_705590
  have hstable : (prefixWord ++ tailWord_705590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705590).length < 2 ^ (prefixWord ++ tailWord_705590).sum := by decide
  have hdescent : baseEnd_705590 < baseStart_705590 := by decide
  rcases family_descends (prefixWord ++ tailWord_705590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705697 : List Nat := [1, 2, 3, 3, 1, 1, 5, 2, 3]
def baseStart_705697 : Nat := 118140960795 + 705697 * 2 ^ 59
def prefixEnd_705697 : Nat := 4983230072969 + 3 ^ 40 * 705697 * 2
def baseEnd_705697 : Nat := 161049669971569195974251

theorem tailTrace_705697 : CollatzResearch.WordTrace tailWord_705697 prefixEnd_705697 161049669971569195974251 := by
  unfold tailWord_705697
  simp only [CollatzResearch.WordTrace]
  refine ⟨25738884124387767297347345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17159256082925178198231563 25738884124387767297347345)
  ·
    refine ⟨19304163093290825473010509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25738884124387767297347345 19304163093290825473010509)
    ·
      refine ⟨7239061159984059552378941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19304163093290825473010509 7239061159984059552378941)
      ·
        refine ⟨2714647934994022332142103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7239061159984059552378941 2714647934994022332142103)
        ·
          refine ⟨4071971902491033498213155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714647934994022332142103 4071971902491033498213155)
          ·
            refine ⟨6107957853736550247319733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071971902491033498213155 6107957853736550247319733)
            ·
              refine ⟨572621048787801585686225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6107957853736550247319733 572621048787801585686225)
              ·
                refine ⟨429465786590851189264669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572621048787801585686225 429465786590851189264669)
                ·
                  refine ⟨161049669971569195974251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429465786590851189264669 161049669971569195974251)
                  ·
                    rfl

theorem cell21_705697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_705697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705697 prefixEnd_705697 := by exact prefixLift 705697
  have htrace : WordTrace (prefixWord ++ tailWord_705697) baseStart_705697 baseEnd_705697 := by
    simpa [prefixWord, tailWord_705697, baseEnd_705697] using wordTrace_append hprefix tailTrace_705697
  have hstable : (prefixWord ++ tailWord_705697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705697).length < 2 ^ (prefixWord ++ tailWord_705697).sum := by decide
  have hdescent : baseEnd_705697 < baseStart_705697 := by decide
  rcases family_descends (prefixWord ++ tailWord_705697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705722 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_705722 : Nat := 118140960795 + 705722 * 2 ^ 59
def prefixEnd_705722 : Nat := 4983230072969 + 3 ^ 40 * 705722 * 2
def baseEnd_705722 : Nat := 161055375312174708057533

theorem tailTrace_705722 : CollatzResearch.WordTrace tailWord_705722 prefixEnd_705722 161055375312174708057533 := by
  unfold tailWord_705722
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434948987324299141751855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17159863966198131044671613 6434948987324299141751855)
  ·
    refine ⟨9652423480986448712627783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6434948987324299141751855 9652423480986448712627783)
    ·
      refine ⟨14478635221479673068941675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9652423480986448712627783 14478635221479673068941675)
      ·
        refine ⟨21717952832219509603412513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14478635221479673068941675 21717952832219509603412513)
        ·
          refine ⟨16288464624164632202559385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21717952832219509603412513 16288464624164632202559385)
          ·
            refine ⟨12216348468123474151919539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16288464624164632202559385 12216348468123474151919539)
            ·
              refine ⟨18324522702185211227879309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12216348468123474151919539 18324522702185211227879309)
              ·
                refine ⟨6871696013319454210454741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18324522702185211227879309 6871696013319454210454741)
                ·
                  refine ⟨161055375312174708057533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6871696013319454210454741 161055375312174708057533)
                  ·
                    rfl

theorem cell21_705722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_705722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705722 prefixEnd_705722 := by exact prefixLift 705722
  have htrace : WordTrace (prefixWord ++ tailWord_705722) baseStart_705722 baseEnd_705722 := by
    simpa [prefixWord, tailWord_705722, baseEnd_705722] using wordTrace_append hprefix tailTrace_705722
  have hstable : (prefixWord ++ tailWord_705722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705722).length < 2 ^ (prefixWord ++ tailWord_705722).sum := by decide
  have hdescent : baseEnd_705722 < baseStart_705722 := by decide
  rcases family_descends (prefixWord ++ tailWord_705722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705748 : List Nat := [2, 4, 1, 4, 2, 1, 2, 2, 3]
def baseStart_705748 : Nat := 118140960795 + 705748 * 2 ^ 59
def prefixEnd_705748 : Nat := 4983230072969 + 3 ^ 40 * 705748 * 2
def baseEnd_705748 : Nat := 161061308866404440624147

theorem tailTrace_705748 : CollatzResearch.WordTrace tailWord_705748 prefixEnd_705748 161061308866404440624147 := by
  unfold tailWord_705748
  simp only [CollatzResearch.WordTrace]
  refine ⟨12870372123601501503726949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17160496164802002004969265 12870372123601501503726949)
  ·
    refine ⟨2413194773175281531948803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12870372123601501503726949 2413194773175281531948803)
    ·
      refine ⟨3619792159762922297923205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2413194773175281531948803 3619792159762922297923205)
      ·
        refine ⟨678711029955547930860601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3619792159762922297923205 678711029955547930860601)
        ·
          refine ⟨509033272466660948145451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 678711029955547930860601 509033272466660948145451)
          ·
            refine ⟨763549908699991422218177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509033272466660948145451 763549908699991422218177)
            ·
              refine ⟨572662431524993566663633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763549908699991422218177 572662431524993566663633)
              ·
                refine ⟨429496823643745174997725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572662431524993566663633 429496823643745174997725)
                ·
                  refine ⟨161061308866404440624147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429496823643745174997725 161061308866404440624147)
                  ·
                    rfl

theorem cell21_705748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_705748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705748 prefixEnd_705748 := by exact prefixLift 705748
  have htrace : WordTrace (prefixWord ++ tailWord_705748) baseStart_705748 baseEnd_705748 := by
    simpa [prefixWord, tailWord_705748, baseEnd_705748] using wordTrace_append hprefix tailTrace_705748
  have hstable : (prefixWord ++ tailWord_705748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705748).length < 2 ^ (prefixWord ++ tailWord_705748).sum := by decide
  have hdescent : baseEnd_705748 < baseStart_705748 := by decide
  rcases family_descends (prefixWord ++ tailWord_705748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705770 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_705770 : Nat := 118140960795 + 705770 * 2 ^ 59
def prefixEnd_705770 : Nat := 4983230072969 + 3 ^ 40 * 705770 * 2
def baseEnd_705770 : Nat := 161066329566137291257435

theorem tailTrace_705770 : CollatzResearch.WordTrace tailWord_705770 prefixEnd_705770 161066329566137291257435 := by
  unfold tailWord_705770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435386663280825191188691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17161031102082200509836509 6435386663280825191188691)
  ·
    refine ⟨9653079994921237786783037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6435386663280825191188691 9653079994921237786783037)
    ·
      refine ⟨3619904998095464170043639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9653079994921237786783037 3619904998095464170043639)
      ·
        refine ⟨5429857497143196255065459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619904998095464170043639 5429857497143196255065459)
        ·
          refine ⟨8144786245714794382598189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429857497143196255065459 8144786245714794382598189)
          ·
            refine ⟨3054294842143047893474321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8144786245714794382598189 3054294842143047893474321)
            ·
              refine ⟨2290721131607285920105741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3054294842143047893474321 2290721131607285920105741)
              ·
                refine ⟨859020424352732220039653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2290721131607285920105741 859020424352732220039653)
                ·
                  refine ⟨161066329566137291257435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859020424352732220039653 161066329566137291257435)
                  ·
                    rfl

theorem cell21_705770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_705770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705770 prefixEnd_705770 := by exact prefixLift 705770
  have htrace : WordTrace (prefixWord ++ tailWord_705770) baseStart_705770 baseEnd_705770 := by
    simpa [prefixWord, tailWord_705770, baseEnd_705770] using wordTrace_append hprefix tailTrace_705770
  have hstable : (prefixWord ++ tailWord_705770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705770).length < 2 ^ (prefixWord ++ tailWord_705770).sum := by decide
  have hdescent : baseEnd_705770 < baseStart_705770 := by decide
  rcases family_descends (prefixWord ++ tailWord_705770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705815 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 5]
def baseStart_705815 : Nat := 118140960795 + 705815 * 2 ^ 59
def prefixEnd_705815 : Nat := 4983230072969 + 3 ^ 40 * 705815 * 2
def baseEnd_705815 : Nat := 161076599179227213007343

theorem tailTrace_705815 : CollatzResearch.WordTrace tailWord_705815 prefixEnd_705815 161076599179227213007343 := by
  unfold tailWord_705815
  simp only [CollatzResearch.WordTrace]
  refine ⟨25743187937960273450142899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17162125291973515633428599 25743187937960273450142899)
  ·
    refine ⟨38614781906940410175214349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25743187937960273450142899 38614781906940410175214349)
    ·
      refine ⟨14480543215102653815705381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38614781906940410175214349 14480543215102653815705381)
      ·
        refine ⟨2715101852831747590444759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14480543215102653815705381 2715101852831747590444759)
        ·
          refine ⟨4072652779247621385667139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2715101852831747590444759 4072652779247621385667139)
          ·
            refine ⟨6108979168871432078500709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072652779247621385667139 6108979168871432078500709)
            ·
              refine ⟨1145433594163393514718883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6108979168871432078500709 1145433594163393514718883)
              ·
                refine ⟨1718150391245090272078325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145433594163393514718883 1718150391245090272078325)
                ·
                  refine ⟨161076599179227213007343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1718150391245090272078325 161076599179227213007343)
                  ·
                    rfl

theorem cell21_705815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_705815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705815 prefixEnd_705815 := by exact prefixLift 705815
  have htrace : WordTrace (prefixWord ++ tailWord_705815) baseStart_705815 baseEnd_705815 := by
    simpa [prefixWord, tailWord_705815, baseEnd_705815] using wordTrace_append hprefix tailTrace_705815
  have hstable : (prefixWord ++ tailWord_705815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705815).length < 2 ^ (prefixWord ++ tailWord_705815).sum := by decide
  have hdescent : baseEnd_705815 < baseStart_705815 := by decide
  rcases family_descends (prefixWord ++ tailWord_705815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705981 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 6]
def baseStart_705981 : Nat := 118140960795 + 705981 * 2 ^ 59
def prefixEnd_705981 : Nat := 4983230072969 + 3 ^ 40 * 705981 * 2
def baseEnd_705981 : Nat := 161114482640847813240337

theorem tailTrace_705981 : CollatzResearch.WordTrace tailWord_705981 prefixEnd_705981 161114482640847813240337 := by
  unfold tailWord_705981
  simp only [CollatzResearch.WordTrace]
  refine ⟨25749242455358883800685797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17166161636905922533790531 25749242455358883800685797)
  ·
    refine ⟨4827982960379790712628587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25749242455358883800685797 4827982960379790712628587)
    ·
      refine ⟨7241974440569686068942881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4827982960379790712628587 7241974440569686068942881)
      ·
        refine ⟨5431480830427264551707161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7241974440569686068942881 5431480830427264551707161)
        ·
          refine ⟨4073610622820448413780371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5431480830427264551707161 4073610622820448413780371)
          ·
            refine ⟨6110415934230672620670557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073610622820448413780371 6110415934230672620670557)
            ·
              refine ⟨2291405975336502232751459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6110415934230672620670557 2291405975336502232751459)
              ·
                refine ⟨3437108963004753349127189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291405975336502232751459 3437108963004753349127189)
                ·
                  refine ⟨161114482640847813240337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3437108963004753349127189 161114482640847813240337)
                  ·
                    rfl

theorem cell21_705981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_705981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_705981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_705981 prefixEnd_705981 := by exact prefixLift 705981
  have htrace : WordTrace (prefixWord ++ tailWord_705981) baseStart_705981 baseEnd_705981 := by
    simpa [prefixWord, tailWord_705981, baseEnd_705981] using wordTrace_append hprefix tailTrace_705981
  have hstable : (prefixWord ++ tailWord_705981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705981).length < 2 ^ (prefixWord ++ tailWord_705981).sum := by decide
  have hdescent : baseEnd_705981 < baseStart_705981 := by decide
  rcases family_descends (prefixWord ++ tailWord_705981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706029 : List Nat := [1, 5, 1, 3, 2, 2, 7]
def baseStart_706029 : Nat := 118140960795 + 706029 * 2 ^ 59
def prefixEnd_706029 : Nat := 4983230072969 + 3 ^ 40 * 706029 * 2
def baseEnd_706029 : Nat := 17902826321645599604471

theorem tailTrace_706029 : CollatzResearch.WordTrace tailWord_706029 prefixEnd_706029 17902826321645599604471 := by
  unfold tailWord_706029
  simp only [CollatzResearch.WordTrace]
  refine ⟨25750993159184987998433141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17167328772789991998955427 25750993159184987998433141)
  ·
    refine ⟨2414155608673592624853107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25750993159184987998433141 2414155608673592624853107)
    ·
      refine ⟨3621233413010388937279661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414155608673592624853107 3621233413010388937279661)
      ·
        refine ⟨1357962529878895851479873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3621233413010388937279661 1357962529878895851479873)
        ·
          refine ⟨1018471897409171888609905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1357962529878895851479873 1018471897409171888609905)
          ·
            refine ⟨763853923056878916457429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018471897409171888609905 763853923056878916457429)
            ·
              refine ⟨17902826321645599604471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 763853923056878916457429 17902826321645599604471)
              ·
                rfl

theorem cell21_706029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 7].length) (baseStart_706029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706029 prefixEnd_706029 := by exact prefixLift 706029
  have htrace : WordTrace (prefixWord ++ tailWord_706029) baseStart_706029 baseEnd_706029 := by
    simpa [prefixWord, tailWord_706029, baseEnd_706029] using wordTrace_append hprefix tailTrace_706029
  have hstable : (prefixWord ++ tailWord_706029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706029).length < 2 ^ (prefixWord ++ tailWord_706029).sum := by decide
  have hdescent : baseEnd_706029 < baseStart_706029 := by decide
  rcases family_descends (prefixWord ++ tailWord_706029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706046 : List Nat := [4, 2, 2, 3, 1, 1, 2, 6]
def baseStart_706046 : Nat := 118140960795 + 706046 * 2 ^ 59
def prefixEnd_706046 : Nat := 4983230072969 + 3 ^ 40 * 706046 * 2
def baseEnd_706046 : Nat := 53709772175474048218957

theorem tailTrace_706046 : CollatzResearch.WordTrace tailWord_706046 prefixEnd_706046 53709772175474048218957 := by
  unfold tailWord_706046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218951650015424987725249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17167742133415599934534661 3218951650015424987725249)
  ·
    refine ⟨2414213737511568740793937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3218951650015424987725249 2414213737511568740793937)
    ·
      refine ⟨1810660303133676555595453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2414213737511568740793937 1810660303133676555595453)
      ·
        refine ⟨678997613675128708348295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1810660303133676555595453 678997613675128708348295)
        ·
          refine ⟨1018496420512693062522443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678997613675128708348295 1018496420512693062522443)
          ·
            refine ⟨1527744630769039593783665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018496420512693062522443 1527744630769039593783665)
            ·
              refine ⟨1145808473076779695337749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527744630769039593783665 1145808473076779695337749)
              ·
                refine ⟨53709772175474048218957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1145808473076779695337749 53709772175474048218957)
                ·
                  rfl

theorem cell21_706046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_706046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706046 prefixEnd_706046 := by exact prefixLift 706046
  have htrace : WordTrace (prefixWord ++ tailWord_706046) baseStart_706046 baseEnd_706046 := by
    simpa [prefixWord, tailWord_706046, baseEnd_706046] using wordTrace_append hprefix tailTrace_706046
  have hstable : (prefixWord ++ tailWord_706046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706046).length < 2 ^ (prefixWord ++ tailWord_706046).sum := by decide
  have hdescent : baseEnd_706046 < baseStart_706046 := by decide
  rcases family_descends (prefixWord ++ tailWord_706046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706057 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 4]
def baseStart_706057 : Nat := 118140960795 + 706057 * 2 ^ 59
def prefixEnd_706057 : Nat := 4983230072969 + 3 ^ 40 * 706057 * 2
def baseEnd_706057 : Nat := 161131826876288569973515

theorem tailTrace_706057 : CollatzResearch.WordTrace tailWord_706057 prefixEnd_706057 161131826876288569973515 := by
  unfold tailWord_706057
  simp only [CollatzResearch.WordTrace]
  refine ⟨25752014403083548780452425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17168009602055699186968283 25752014403083548780452425)
  ·
    refine ⟨19314010802312661585339319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25752014403083548780452425 19314010802312661585339319)
    ·
      refine ⟨28971016203468992378008979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19314010802312661585339319 28971016203468992378008979)
      ·
        refine ⟨43456524305203488567013469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28971016203468992378008979 43456524305203488567013469)
        ·
          refine ⟨16296196614451308212630051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43456524305203488567013469 16296196614451308212630051)
          ·
            refine ⟨24444294921676962318945077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16296196614451308212630051 24444294921676962318945077)
            ·
              refine ⟨2291652648907215217401101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24444294921676962318945077 2291652648907215217401101)
              ·
                refine ⟨859369743340205706525413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2291652648907215217401101 859369743340205706525413)
                ·
                  refine ⟨161131826876288569973515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859369743340205706525413 161131826876288569973515)
                  ·
                    rfl

theorem cell21_706057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_706057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706057 prefixEnd_706057 := by exact prefixLift 706057
  have htrace : WordTrace (prefixWord ++ tailWord_706057) baseStart_706057 baseEnd_706057 := by
    simpa [prefixWord, tailWord_706057, baseEnd_706057] using wordTrace_append hprefix tailTrace_706057
  have hstable : (prefixWord ++ tailWord_706057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706057).length < 2 ^ (prefixWord ++ tailWord_706057).sum := by decide
  have hdescent : baseEnd_706057 < baseStart_706057 := by decide
  rcases family_descends (prefixWord ++ tailWord_706057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706088 : List Nat := [2, 1, 5, 2, 2, 9]
def baseStart_706088 : Nat := 118140960795 + 706088 * 2 ^ 59
def prefixEnd_706088 : Nat := 4983230072969 + 3 ^ 40 * 706088 * 2
def baseEnd_706088 : Nat := 5968107462912570553955

theorem tailTrace_706088 : CollatzResearch.WordTrace tailWord_706088 prefixEnd_706088 5968107462912570553955 := by
  unfold tailWord_706088
  simp only [CollatzResearch.WordTrace]
  refine ⟨12876572532985620537415459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17168763377314160716553945 12876572532985620537415459)
  ·
    refine ⟨19314858799478430806123189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12876572532985620537415459 19314858799478430806123189)
    ·
      refine ⟨1810768012451102888074049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19314858799478430806123189 1810768012451102888074049)
      ·
        refine ⟨1358076009338327166055537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1810768012451102888074049 1358076009338327166055537)
        ·
          refine ⟨1018557007003745374541653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1358076009338327166055537 1018557007003745374541653)
          ·
            refine ⟨5968107462912570553955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1018557007003745374541653 5968107462912570553955)
            ·
              rfl

theorem cell21_706088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 9].length) (baseStart_706088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706088 prefixEnd_706088 := by exact prefixLift 706088
  have htrace : WordTrace (prefixWord ++ tailWord_706088) baseStart_706088 baseEnd_706088 := by
    simpa [prefixWord, tailWord_706088, baseEnd_706088] using wordTrace_append hprefix tailTrace_706088
  have hstable : (prefixWord ++ tailWord_706088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706088).length < 2 ^ (prefixWord ++ tailWord_706088).sum := by decide
  have hdescent : baseEnd_706088 < baseStart_706088 := by decide
  rcases family_descends (prefixWord ++ tailWord_706088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706094 : List Nat := [4, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_706094 : Nat := 118140960795 + 706094 * 2 ^ 59
def prefixEnd_706094 : Nat := 4983230072969 + 3 ^ 40 * 706094 * 2
def baseEnd_706094 : Nat := 161140270780384727856773

theorem tailTrace_706094 : CollatzResearch.WordTrace tailWord_706094 prefixEnd_706094 161140270780384727856773 := by
  unfold tailWord_706094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219170487993688012443667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17168909269299669399699557 3219170487993688012443667)
  ·
    refine ⟨4828755731990532018665501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3219170487993688012443667 4828755731990532018665501)
    ·
      refine ⟨1810783399496449506999563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4828755731990532018665501 1810783399496449506999563)
      ·
        refine ⟨2716175099244674260499345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810783399496449506999563 2716175099244674260499345)
        ·
          refine ⟨2037131324433505695374509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716175099244674260499345 2037131324433505695374509)
          ·
            refine ⟨763924246662564635765441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2037131324433505695374509 763924246662564635765441)
            ·
              refine ⟨572943184996923476824081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763924246662564635765441 572943184996923476824081)
              ·
                refine ⟨429707388747692607618061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572943184996923476824081 429707388747692607618061)
                ·
                  refine ⟨161140270780384727856773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429707388747692607618061 161140270780384727856773)
                  ·
                    rfl

theorem cell21_706094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_706094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706094 prefixEnd_706094 := by exact prefixLift 706094
  have htrace : WordTrace (prefixWord ++ tailWord_706094) baseStart_706094 baseEnd_706094 := by
    simpa [prefixWord, tailWord_706094, baseEnd_706094] using wordTrace_append hprefix tailTrace_706094
  have hstable : (prefixWord ++ tailWord_706094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706094).length < 2 ^ (prefixWord ++ tailWord_706094).sum := by decide
  have hdescent : baseEnd_706094 < baseStart_706094 := by decide
  rcases family_descends (prefixWord ++ tailWord_706094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706119 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 5]
def baseStart_706119 : Nat := 118140960795 + 706119 * 2 ^ 59
def prefixEnd_706119 : Nat := 4983230072969 + 3 ^ 40 * 706119 * 2
def baseEnd_706119 : Nat := 161145976120990239940055

theorem tailTrace_706119 : CollatzResearch.WordTrace tailWord_706119 prefixEnd_706119 161145976120990239940055 := by
  unfold tailWord_706119
  simp only [CollatzResearch.WordTrace]
  refine ⟨25754275728858933369209411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17169517152572622246139607 25754275728858933369209411)
  ·
    refine ⟨38631413593288400053814117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25754275728858933369209411 38631413593288400053814117)
    ·
      refine ⟨7243390048741575010090147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38631413593288400053814117 7243390048741575010090147)
      ·
        refine ⟨10865085073112362515135221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7243390048741575010090147 10865085073112362515135221)
        ·
          refine ⟨1018601725604283985793927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10865085073112362515135221 1018601725604283985793927)
          ·
            refine ⟨1527902588406425978690891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018601725604283985793927 1527902588406425978690891)
            ·
              refine ⟨2291853882609638968036337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527902588406425978690891 2291853882609638968036337)
              ·
                refine ⟨1718890411957229226027253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291853882609638968036337 1718890411957229226027253)
                ·
                  refine ⟨161145976120990239940055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1718890411957229226027253 161145976120990239940055)
                  ·
                    rfl

theorem cell21_706119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_706119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706119 prefixEnd_706119 := by exact prefixLift 706119
  have htrace : WordTrace (prefixWord ++ tailWord_706119) baseStart_706119 baseEnd_706119 := by
    simpa [prefixWord, tailWord_706119, baseEnd_706119] using wordTrace_append hprefix tailTrace_706119
  have hstable : (prefixWord ++ tailWord_706119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706119).length < 2 ^ (prefixWord ++ tailWord_706119).sum := by decide
  have hdescent : baseEnd_706119 < baseStart_706119 := by decide
  rcases family_descends (prefixWord ++ tailWord_706119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706147 : List Nat := [1, 1, 1, 5, 1, 4, 8]
def baseStart_706147 : Nat := 118140960795 + 706147 * 2 ^ 59
def prefixEnd_706147 : Nat := 4983230072969 + 3 ^ 40 * 706147 * 2
def baseEnd_706147 : Nat := 17905818455829823719259

theorem tailTrace_706147 : CollatzResearch.WordTrace tailWord_706147 prefixEnd_706147 17905818455829823719259 := by
  unfold tailWord_706147
  simp only [CollatzResearch.WordTrace]
  refine ⟨25755296972757494151228695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17170197981838329434152463 25755296972757494151228695)
  ·
    refine ⟨38632945459136241226843043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25755296972757494151228695 38632945459136241226843043)
    ·
      refine ⟨57949418188704361840264565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38632945459136241226843043 57949418188704361840264565)
      ·
        refine ⟨5432757955191033922524803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57949418188704361840264565 5432757955191033922524803)
        ·
          refine ⟨8149136932786550883787205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432757955191033922524803 8149136932786550883787205)
          ·
            refine ⟨1527963174897478290710101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8149136932786550883787205 1527963174897478290710101)
            ·
              refine ⟨17905818455829823719259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1527963174897478290710101 17905818455829823719259)
              ·
                rfl

theorem cell21_706147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 8].length) (baseStart_706147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706147 prefixEnd_706147 := by exact prefixLift 706147
  have htrace : WordTrace (prefixWord ++ tailWord_706147) baseStart_706147 baseEnd_706147 := by
    simpa [prefixWord, tailWord_706147, baseEnd_706147] using wordTrace_append hprefix tailTrace_706147
  have hstable : (prefixWord ++ tailWord_706147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706147).length < 2 ^ (prefixWord ++ tailWord_706147).sum := by decide
  have hdescent : baseEnd_706147 < baseStart_706147 := by decide
  rcases family_descends (prefixWord ++ tailWord_706147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706209 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 6]
def baseStart_706209 : Nat := 118140960795 + 706209 * 2 ^ 59
def prefixEnd_706209 : Nat := 4983230072969 + 3 ^ 40 * 706209 * 2
def baseEnd_706209 : Nat := 161166515347170083439871

theorem tailTrace_706209 : CollatzResearch.WordTrace tailWord_706209 prefixEnd_706209 161166515347170083439871 := by
  unfold tailWord_706209
  simp only [CollatzResearch.WordTrace]
  refine ⟨25757558298532878739985681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17171705532355252493323787 25757558298532878739985681)
  ·
    refine ⟨19318168723899659054989261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25757558298532878739985681 19318168723899659054989261)
    ·
      refine ⟨7244313271462372145620973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19318168723899659054989261 7244313271462372145620973)
      ·
        refine ⟨2716617476798389554607865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7244313271462372145620973 2716617476798389554607865)
        ·
          refine ⟨2037463107598792165955899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716617476798389554607865 2037463107598792165955899)
          ·
            refine ⟨3056194661398188248933849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037463107598792165955899 3056194661398188248933849)
            ·
              refine ⟨2292145996048641186700387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056194661398188248933849 2292145996048641186700387)
              ·
                refine ⟨3438218994072961780050581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292145996048641186700387 3438218994072961780050581)
                ·
                  refine ⟨161166515347170083439871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3438218994072961780050581 161166515347170083439871)
                  ·
                    rfl

theorem cell21_706209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_706209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706209 prefixEnd_706209 := by exact prefixLift 706209
  have htrace : WordTrace (prefixWord ++ tailWord_706209) baseStart_706209 baseEnd_706209 := by
    simpa [prefixWord, tailWord_706209, baseEnd_706209] using wordTrace_append hprefix tailTrace_706209
  have hstable : (prefixWord ++ tailWord_706209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706209).length < 2 ^ (prefixWord ++ tailWord_706209).sum := by decide
  have hdescent : baseEnd_706209 < baseStart_706209 := by decide
  rcases family_descends (prefixWord ++ tailWord_706209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706223 : List Nat := [1, 1, 2, 1, 2, 4, 4, 6]
def baseStart_706223 : Nat := 118140960795 + 706223 * 2 ^ 59
def prefixEnd_706223 : Nat := 4983230072969 + 3 ^ 40 * 706223 * 2
def baseEnd_706223 : Nat := 53723236779303056735503

theorem tailTrace_706223 : CollatzResearch.WordTrace tailWord_706223 prefixEnd_706223 53723236779303056735503 := by
  unfold tailWord_706223
  simp only [CollatzResearch.WordTrace]
  refine ⟨25758068920482159130995323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17172045946988106087330215 25758068920482159130995323)
  ·
    refine ⟨38637103380723238696492985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25758068920482159130995323 38637103380723238696492985)
    ·
      refine ⟨28977827535542429022369739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38637103380723238696492985 28977827535542429022369739)
      ·
        refine ⟨43466741303313643533554609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28977827535542429022369739 43466741303313643533554609)
        ·
          refine ⟨32600055977485232650165957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43466741303313643533554609 32600055977485232650165957)
          ·
            refine ⟨6112510495778481121906117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32600055977485232650165957 6112510495778481121906117)
            ·
              refine ⟨1146095717958465210357397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6112510495778481121906117 1146095717958465210357397)
              ·
                refine ⟨53723236779303056735503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1146095717958465210357397 53723236779303056735503)
                ·
                  rfl

theorem cell21_706223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 6].length) (baseStart_706223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706223 prefixEnd_706223 := by exact prefixLift 706223
  have htrace : WordTrace (prefixWord ++ tailWord_706223) baseStart_706223 baseEnd_706223 := by
    simpa [prefixWord, tailWord_706223, baseEnd_706223] using wordTrace_append hprefix tailTrace_706223
  have hstable : (prefixWord ++ tailWord_706223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706223).length < 2 ^ (prefixWord ++ tailWord_706223).sum := by decide
  have hdescent : baseEnd_706223 < baseStart_706223 := by decide
  rcases family_descends (prefixWord ++ tailWord_706223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706226 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_706226 : Nat := 118140960795 + 706226 * 2 ^ 59
def prefixEnd_706226 : Nat := 4983230072969 + 3 ^ 40 * 706226 * 2
def baseEnd_706226 : Nat := 161170394978781831656503

theorem tailTrace_706226 : CollatzResearch.WordTrace tailWord_706226 prefixEnd_706226 161170394978781831656503 := by
  unfold tailWord_706226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6439544584867822660838633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17172118892980860428903021 6439544584867822660838633)
  ·
    refine ⟨4829658438650866995628975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6439544584867822660838633 4829658438650866995628975)
    ·
      refine ⟨7244487657976300493443463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4829658438650866995628975 7244487657976300493443463)
      ·
        refine ⟨10866731486964450740165195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7244487657976300493443463 10866731486964450740165195)
        ·
          refine ⟨16300097230446676110247793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10866731486964450740165195 16300097230446676110247793)
          ·
            refine ⟨12225072922835007082685845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16300097230446676110247793 12225072922835007082685845)
            ·
              refine ⟨573050293257890957000899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12225072922835007082685845 573050293257890957000899)
              ·
                refine ⟨859575439886836435501349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573050293257890957000899 859575439886836435501349)
                ·
                  refine ⟨161170394978781831656503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859575439886836435501349 161170394978781831656503)
                  ·
                    rfl

theorem cell21_706226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_706226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706226 prefixEnd_706226 := by exact prefixLift 706226
  have htrace : WordTrace (prefixWord ++ tailWord_706226) baseStart_706226 baseEnd_706226 := by
    simpa [prefixWord, tailWord_706226, baseEnd_706226] using wordTrace_append hprefix tailTrace_706226
  have hstable : (prefixWord ++ tailWord_706226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706226).length < 2 ^ (prefixWord ++ tailWord_706226).sum := by decide
  have hdescent : baseEnd_706226 < baseStart_706226 := by decide
  rcases family_descends (prefixWord ++ tailWord_706226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706271 : List Nat := [1, 1, 2, 3, 2, 2, 3, 4, 3]
def baseStart_706271 : Nat := 118140960795 + 706271 * 2 ^ 59
def prefixEnd_706271 : Nat := 4983230072969 + 3 ^ 40 * 706271 * 2
def baseEnd_706271 : Nat := 161180664591871753406411

theorem tailTrace_706271 : CollatzResearch.WordTrace tailWord_706271 prefixEnd_706271 161180664591871753406411 := by
  unfold tailWord_706271
  simp only [CollatzResearch.WordTrace]
  refine ⟨25759819624308263328742667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17173213082872175552495111 25759819624308263328742667)
  ·
    refine ⟨38639729436462394993114001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25759819624308263328742667 38639729436462394993114001)
    ·
      refine ⟨28979797077346796244835501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38639729436462394993114001 28979797077346796244835501)
      ·
        refine ⟨10867423904005048591813313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28979797077346796244835501 10867423904005048591813313)
        ·
          refine ⟨8150567928003786443859985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10867423904005048591813313 8150567928003786443859985)
          ·
            refine ⟨6112925946002839832894989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8150567928003786443859985 6112925946002839832894989)
            ·
              refine ⟨2292347229751064937335621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6112925946002839832894989 2292347229751064937335621)
              ·
                refine ⟨429815105578324675750429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2292347229751064937335621 429815105578324675750429)
                ·
                  refine ⟨161180664591871753406411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429815105578324675750429 161180664591871753406411)
                  ·
                    rfl

theorem cell21_706271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 3].length) (baseStart_706271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706271 prefixEnd_706271 := by exact prefixLift 706271
  have htrace : WordTrace (prefixWord ++ tailWord_706271) baseStart_706271 baseEnd_706271 := by
    simpa [prefixWord, tailWord_706271, baseEnd_706271] using wordTrace_append hprefix tailTrace_706271
  have hstable : (prefixWord ++ tailWord_706271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706271).length < 2 ^ (prefixWord ++ tailWord_706271).sum := by decide
  have hdescent : baseEnd_706271 < baseStart_706271 := by decide
  rcases family_descends (prefixWord ++ tailWord_706271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706313 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 9]
def baseStart_706313 : Nat := 118140960795 + 706313 * 2 ^ 59
def prefixEnd_706313 : Nat := 4983230072969 + 3 ^ 40 * 706313 * 2
def baseEnd_706313 : Nat := 161190249564089013706325

theorem tailTrace_706313 : CollatzResearch.WordTrace tailWord_706313 prefixEnd_706313 161190249564089013706325 := by
  unfold tailWord_706313
  simp only [CollatzResearch.WordTrace]
  refine ⟨25761351490156104501771593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17174234326770736334514395 25761351490156104501771593)
  ·
    refine ⟨19321013617617078376328695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25761351490156104501771593 19321013617617078376328695)
    ·
      refine ⟨28981520426425617564493043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19321013617617078376328695 28981520426425617564493043)
      ·
        refine ⟨43472280639638426346739565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28981520426425617564493043 43472280639638426346739565)
        ·
          refine ⟨16302105239864409880027337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43472280639638426346739565 16302105239864409880027337)
          ·
            refine ⟨12226578929898307410020503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16302105239864409880027337 12226578929898307410020503)
            ·
              refine ⟨18339868394847461115030755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12226578929898307410020503 18339868394847461115030755)
              ·
                refine ⟨27509802592271191672546133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18339868394847461115030755 27509802592271191672546133)
                ·
                  refine ⟨161190249564089013706325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27509802592271191672546133 161190249564089013706325)
                  ·
                    rfl

theorem cell21_706313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_706313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706313 prefixEnd_706313 := by exact prefixLift 706313
  have htrace : WordTrace (prefixWord ++ tailWord_706313) baseStart_706313 baseEnd_706313 := by
    simpa [prefixWord, tailWord_706313, baseEnd_706313] using wordTrace_append hprefix tailTrace_706313
  have hstable : (prefixWord ++ tailWord_706313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706313).length < 2 ^ (prefixWord ++ tailWord_706313).sum := by decide
  have hdescent : baseEnd_706313 < baseStart_706313 := by decide
  rcases family_descends (prefixWord ++ tailWord_706313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706330 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_706330 : Nat := 118140960795 + 706330 * 2 ^ 59
def prefixEnd_706330 : Nat := 4983230072969 + 3 ^ 40 * 706330 * 2
def baseEnd_706330 : Nat := 161194129195700761922957

theorem tailTrace_706330 : CollatzResearch.WordTrace tailWord_706330 prefixEnd_706330 161194129195700761922957 := by
  unfold tailWord_706330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6440492882773629101285111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17174647687396344270093629 6440492882773629101285111)
  ·
    refine ⟨9660739324160443651927667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6440492882773629101285111 9660739324160443651927667)
    ·
      refine ⟨14491108986240665477891501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9660739324160443651927667 14491108986240665477891501)
      ·
        refine ⟨5434165869840249554209313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14491108986240665477891501 5434165869840249554209313)
        ·
          refine ⟨4075624402380187165656985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5434165869840249554209313 4075624402380187165656985)
          ·
            refine ⟨3056718301785140374242739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4075624402380187165656985 3056718301785140374242739)
            ·
              refine ⟨4585077452677710561364109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056718301785140374242739 4585077452677710561364109)
              ·
                refine ⟨1719404044754141460511541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4585077452677710561364109 1719404044754141460511541)
                ·
                  refine ⟨161194129195700761922957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1719404044754141460511541 161194129195700761922957)
                  ·
                    rfl

theorem cell21_706330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_706330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706330 prefixEnd_706330 := by exact prefixLift 706330
  have htrace : WordTrace (prefixWord ++ tailWord_706330) baseStart_706330 baseEnd_706330 := by
    simpa [prefixWord, tailWord_706330, baseEnd_706330] using wordTrace_append hprefix tailTrace_706330
  have hstable : (prefixWord ++ tailWord_706330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706330).length < 2 ^ (prefixWord ++ tailWord_706330).sum := by decide
  have hdescent : baseEnd_706330 < baseStart_706330 := by decide
  rcases family_descends (prefixWord ++ tailWord_706330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706350 : List Nat := [4, 1, 3, 2, 2, 2, 2, 5]
def baseStart_706350 : Nat := 118140960795 + 706350 * 2 ^ 59
def prefixEnd_706350 : Nat := 4983230072969 + 3 ^ 40 * 706350 * 2
def baseEnd_706350 : Nat := 53732897822728390529861

theorem tailTrace_706350 : CollatzResearch.WordTrace tailWord_706350 prefixEnd_706350 53732897822728390529861 := by
  unfold tailWord_706350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220337623877757477608563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17175133994014706547245669 3220337623877757477608563)
  ·
    refine ⟨4830506435816636216412845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3220337623877757477608563 4830506435816636216412845)
    ·
      refine ⟨1811439913431238581154817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4830506435816636216412845 1811439913431238581154817)
      ·
        refine ⟨1358579935073428935866113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1811439913431238581154817 1358579935073428935866113)
        ·
          refine ⟨1018934951305071701899585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1358579935073428935866113 1018934951305071701899585)
          ·
            refine ⟨764201213478803776424689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018934951305071701899585 764201213478803776424689)
            ·
              refine ⟨573150910109102832318517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 764201213478803776424689 573150910109102832318517)
              ·
                refine ⟨53732897822728390529861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 573150910109102832318517 53732897822728390529861)
                ·
                  rfl

theorem cell21_706350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_706350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706350 prefixEnd_706350 := by exact prefixLift 706350
  have htrace : WordTrace (prefixWord ++ tailWord_706350) baseStart_706350 baseEnd_706350 := by
    simpa [prefixWord, tailWord_706350, baseEnd_706350] using wordTrace_append hprefix tailTrace_706350
  have hstable : (prefixWord ++ tailWord_706350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706350).length < 2 ^ (prefixWord ++ tailWord_706350).sum := by decide
  have hdescent : baseEnd_706350 < baseStart_706350 := by decide
  rcases family_descends (prefixWord ++ tailWord_706350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706437 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 4]
def baseStart_706437 : Nat := 118140960795 + 706437 * 2 ^ 59
def prefixEnd_706437 : Nat := 4983230072969 + 3 ^ 40 * 706437 * 2
def baseEnd_706437 : Nat := 161218548053492353639405

theorem tailTrace_706437 : CollatzResearch.WordTrace tailWord_706437 prefixEnd_706437 161218548053492353639405 := by
  unfold tailWord_706437
  simp only [CollatzResearch.WordTrace]
  refine ⟨25765874141706873679285565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17177249427804582452857043 25765874141706873679285565)
  ·
    refine ⟨9662202803140077629732087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25765874141706873679285565 9662202803140077629732087)
    ·
      refine ⟨14493304204710116444598131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9662202803140077629732087 14493304204710116444598131)
      ·
        refine ⟨21739956307065174666897197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14493304204710116444598131 21739956307065174666897197)
        ·
          refine ⟨8152483615149440500086449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21739956307065174666897197 8152483615149440500086449)
          ·
            refine ⟨6114362711362080375064837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8152483615149440500086449 6114362711362080375064837)
            ·
              refine ⟨1146443008380390070324657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6114362711362080375064837 1146443008380390070324657)
              ·
                refine ⟨859832256285292552743493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146443008380390070324657 859832256285292552743493)
                ·
                  refine ⟨161218548053492353639405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859832256285292552743493 161218548053492353639405)
                  ·
                    rfl

theorem cell21_706437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_706437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706437 prefixEnd_706437 := by exact prefixLift 706437
  have htrace : WordTrace (prefixWord ++ tailWord_706437) baseStart_706437 baseEnd_706437 := by
    simpa [prefixWord, tailWord_706437, baseEnd_706437] using wordTrace_append hprefix tailTrace_706437
  have hstable : (prefixWord ++ tailWord_706437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706437).length < 2 ^ (prefixWord ++ tailWord_706437).sum := by decide
  have hdescent : baseEnd_706437 < baseStart_706437 := by decide
  rcases family_descends (prefixWord ++ tailWord_706437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706440 : List Nat := [2, 1, 3, 3, 3, 1, 1, 4, 3]
def baseStart_706440 : Nat := 118140960795 + 706440 * 2 ^ 59
def prefixEnd_706440 : Nat := 4983230072969 + 3 ^ 40 * 706440 * 2
def baseEnd_706440 : Nat := 161219232694365015089399

theorem tailTrace_706440 : CollatzResearch.WordTrace tailWord_706440 prefixEnd_706440 161219232694365015089399 := by
  unfold tailWord_706440
  simp only [CollatzResearch.WordTrace]
  refine ⟨12882991780348002595822387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17177322373797336794429849 12882991780348002595822387)
  ·
    refine ⟨19324487670522003893733581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12882991780348002595822387 19324487670522003893733581)
    ·
      refine ⟨7246682876445751460150093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19324487670522003893733581 7246682876445751460150093)
      ·
        refine ⟨2717506078667156797556285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7246682876445751460150093 2717506078667156797556285)
        ·
          refine ⟨1019064779500183799083607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2717506078667156797556285 1019064779500183799083607)
          ·
            refine ⟨1528597169250275698625411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019064779500183799083607 1528597169250275698625411)
            ·
              refine ⟨2292895753875413547938117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528597169250275698625411 2292895753875413547938117)
              ·
                refine ⟨429917953851640040238397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2292895753875413547938117 429917953851640040238397)
                ·
                  refine ⟨161219232694365015089399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429917953851640040238397 161219232694365015089399)
                  ·
                    rfl

theorem cell21_706440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_706440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706440 prefixEnd_706440 := by exact prefixLift 706440
  have htrace : WordTrace (prefixWord ++ tailWord_706440) baseStart_706440 baseEnd_706440 := by
    simpa [prefixWord, tailWord_706440, baseEnd_706440] using wordTrace_append hprefix tailTrace_706440
  have hstable : (prefixWord ++ tailWord_706440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706440).length < 2 ^ (prefixWord ++ tailWord_706440).sum := by decide
  have hdescent : baseEnd_706440 < baseStart_706440 := by decide
  rcases family_descends (prefixWord ++ tailWord_706440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706468 : List Nat := [2, 3, 1, 2, 1, 4, 3, 5]
def baseStart_706468 : Nat := 118140960795 + 706468 * 2 ^ 59
def prefixEnd_706468 : Nat := 4983230072969 + 3 ^ 40 * 706468 * 2
def baseEnd_706468 : Nat := 53741874225281062874225

theorem tailTrace_706468 : CollatzResearch.WordTrace tailWord_706468 prefixEnd_706468 53741874225281062874225 := by
  unfold tailWord_706468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12883502402297282986832029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17178003203063043982442705 12883502402297282986832029)
  ·
    refine ⟨4831313400861481120062011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12883502402297282986832029 4831313400861481120062011)
    ·
      refine ⟨7246970101292221680093017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4831313400861481120062011 7246970101292221680093017)
      ·
        refine ⟨5435227575969166260069763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7246970101292221680093017 5435227575969166260069763)
        ·
          refine ⟨8152841363953749390104645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5435227575969166260069763 8152841363953749390104645)
          ·
            refine ⟨1528657755741328010644621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8152841363953749390104645 1528657755741328010644621)
            ·
              refine ⟨573246658402998003991733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1528657755741328010644621 573246658402998003991733)
              ·
                refine ⟨53741874225281062874225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 573246658402998003991733 53741874225281062874225)
                ·
                  rfl

theorem cell21_706468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_706468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706468 prefixEnd_706468 := by exact prefixLift 706468
  have htrace : WordTrace (prefixWord ++ tailWord_706468) baseStart_706468 baseEnd_706468 := by
    simpa [prefixWord, tailWord_706468, baseEnd_706468] using wordTrace_append hprefix tailTrace_706468
  have hstable : (prefixWord ++ tailWord_706468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706468).length < 2 ^ (prefixWord ++ tailWord_706468).sum := by decide
  have hdescent : baseEnd_706468 < baseStart_706468 := by decide
  rcases family_descends (prefixWord ++ tailWord_706468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706496 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_706496 : Nat := 118140960795 + 706496 * 2 ^ 59
def prefixEnd_706496 : Nat := 4983230072969 + 3 ^ 40 * 706496 * 2
def baseEnd_706496 : Nat := 161232012657321362155951

theorem tailTrace_706496 : CollatzResearch.WordTrace tailWord_706496 prefixEnd_706496 161232012657321362155951 := by
  unfold tailWord_706496
  simp only [CollatzResearch.WordTrace]
  refine ⟨12884013024246563377841671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17178684032328751170455561 12884013024246563377841671)
  ·
    refine ⟨19326019536369845066762507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12884013024246563377841671 19326019536369845066762507)
    ·
      refine ⟨28989029304554767600143761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19326019536369845066762507 28989029304554767600143761)
      ·
        refine ⟨21741771978416075700107821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28989029304554767600143761 21741771978416075700107821)
        ·
          refine ⟨8153164491906028387540433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21741771978416075700107821 8153164491906028387540433)
          ·
            refine ⟨6114873368929521290655325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8153164491906028387540433 6114873368929521290655325)
            ·
              refine ⟨2293077513348570483995747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6114873368929521290655325 2293077513348570483995747)
              ·
                refine ⟨3439616270022855725993621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293077513348570483995747 3439616270022855725993621)
                ·
                  refine ⟨161232012657321362155951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3439616270022855725993621 161232012657321362155951)
                  ·
                    rfl

theorem cell21_706496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_706496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706496 prefixEnd_706496 := by exact prefixLift 706496
  have htrace : WordTrace (prefixWord ++ tailWord_706496) baseStart_706496 baseEnd_706496 := by
    simpa [prefixWord, tailWord_706496, baseEnd_706496] using wordTrace_append hprefix tailTrace_706496
  have hstable : (prefixWord ++ tailWord_706496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706496).length < 2 ^ (prefixWord ++ tailWord_706496).sum := by decide
  have hdescent : baseEnd_706496 < baseStart_706496 := by decide
  rcases family_descends (prefixWord ++ tailWord_706496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706527 : List Nat := [1, 1, 2, 3, 4, 2, 1, 7]
def baseStart_706527 : Nat := 118140960795 + 706527 * 2 ^ 59
def prefixEnd_706527 : Nat := 4983230072969 + 3 ^ 40 * 706527 * 2
def baseEnd_706527 : Nat := 53746362426557399046407

theorem tailTrace_706527 : CollatzResearch.WordTrace tailWord_706527 prefixEnd_706527 53746362426557399046407 := by
  unfold tailWord_706527
  simp only [CollatzResearch.WordTrace]
  refine ⟨25769156711380819050061835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17179437807587212700041223 25769156711380819050061835)
  ·
    refine ⟨38653735067071228575092753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25769156711380819050061835 38653735067071228575092753)
    ·
      refine ⟨28990301300303421431319565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38653735067071228575092753 28990301300303421431319565)
      ·
        refine ⟨10871362987613783036744837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28990301300303421431319565 10871362987613783036744837)
        ·
          refine ⟨2038380560177584319389657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10871362987613783036744837 2038380560177584319389657)
          ·
            refine ⟨1528785420133188239542243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038380560177584319389657 1528785420133188239542243)
            ·
              refine ⟨2293178130199782359313365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528785420133188239542243 2293178130199782359313365)
              ·
                refine ⟨53746362426557399046407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2293178130199782359313365 53746362426557399046407)
                ·
                  rfl

theorem cell21_706527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 7].length) (baseStart_706527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706527 prefixEnd_706527 := by exact prefixLift 706527
  have htrace : WordTrace (prefixWord ++ tailWord_706527) baseStart_706527 baseEnd_706527 := by
    simpa [prefixWord, tailWord_706527, baseEnd_706527] using wordTrace_append hprefix tailTrace_706527
  have hstable : (prefixWord ++ tailWord_706527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706527).length < 2 ^ (prefixWord ++ tailWord_706527).sum := by decide
  have hdescent : baseEnd_706527 < baseStart_706527 := by decide
  rcases family_descends (prefixWord ++ tailWord_706527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706564 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_706564 : Nat := 118140960795 + 706564 * 2 ^ 59
def prefixEnd_706564 : Nat := 4983230072969 + 3 ^ 40 * 706564 * 2
def baseEnd_706564 : Nat := 161247531183768355022479

theorem tailTrace_706564 : CollatzResearch.WordTrace tailWord_706564 prefixEnd_706564 161247531183768355022479 := by
  unfold tailWord_706564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12885253106123387184579373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17180337474831182912772497 12885253106123387184579373)
  ·
    refine ⟨4831969914796270194217265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12885253106123387184579373 4831969914796270194217265)
    ·
      refine ⟨3623977436097202645662949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4831969914796270194217265 3623977436097202645662949)
      ·
        refine ⟨679495769268225496061803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3623977436097202645662949 679495769268225496061803)
        ·
          refine ⟨1019243653902338244092705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679495769268225496061803 1019243653902338244092705)
          ·
            refine ⟨764432740426753683069529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019243653902338244092705 764432740426753683069529)
            ·
              refine ⟨573324555320065262302147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 764432740426753683069529 573324555320065262302147)
              ·
                refine ⟨859986832980097893453221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573324555320065262302147 859986832980097893453221)
                ·
                  refine ⟨161247531183768355022479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859986832980097893453221 161247531183768355022479)
                  ·
                    rfl

theorem cell21_706564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_706564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706564 prefixEnd_706564 := by exact prefixLift 706564
  have htrace : WordTrace (prefixWord ++ tailWord_706564) baseStart_706564 baseEnd_706564 := by
    simpa [prefixWord, tailWord_706564, baseEnd_706564] using wordTrace_append hprefix tailTrace_706564
  have hstable : (prefixWord ++ tailWord_706564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706564).length < 2 ^ (prefixWord ++ tailWord_706564).sum := by decide
  have hdescent : baseEnd_706564 < baseStart_706564 := by decide
  rcases family_descends (prefixWord ++ tailWord_706564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706606 : List Nat := [4, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_706606 : Nat := 118140960795 + 706606 * 2 ^ 59
def prefixEnd_706606 : Nat := 4983230072969 + 3 ^ 40 * 706606 * 2
def baseEnd_706606 : Nat := 161257116155985615322393

theorem tailTrace_706606 : CollatzResearch.WordTrace tailWord_706606 prefixEnd_706606 161257116155985615322393 := by
  unfold tailWord_706606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221504759761826942773459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17181358718729743694791781 3221504759761826942773459)
  ·
    refine ⟨4832257139642740414160189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221504759761826942773459 4832257139642740414160189)
    ·
      refine ⟨1812096427366027655310071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4832257139642740414160189 1812096427366027655310071)
      ·
        refine ⟨2718144641049041482965107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812096427366027655310071 2718144641049041482965107)
        ·
          refine ⟨4077216961573562224447661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718144641049041482965107 4077216961573562224447661)
          ·
            refine ⟨1528956360590085834167873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4077216961573562224447661 1528956360590085834167873)
            ·
              refine ⟨1146717270442564375625905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528956360590085834167873 1146717270442564375625905)
              ·
                refine ⟨860037952831923281719429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146717270442564375625905 860037952831923281719429)
                ·
                  refine ⟨161257116155985615322393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 860037952831923281719429 161257116155985615322393)
                  ·
                    rfl

theorem cell21_706606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_706606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706606 prefixEnd_706606 := by exact prefixLift 706606
  have htrace : WordTrace (prefixWord ++ tailWord_706606) baseStart_706606 baseEnd_706606 := by
    simpa [prefixWord, tailWord_706606, baseEnd_706606] using wordTrace_append hprefix tailTrace_706606
  have hstable : (prefixWord ++ tailWord_706606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706606).length < 2 ^ (prefixWord ++ tailWord_706606).sum := by decide
  have hdescent : baseEnd_706606 < baseStart_706606 := by decide
  rcases family_descends (prefixWord ++ tailWord_706606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706696 : List Nat := [2, 1, 3, 4, 1, 1, 4, 5]
def baseStart_706696 : Nat := 118140960795 + 706696 * 2 ^ 59
def prefixEnd_706696 : Nat := 4983230072969 + 3 ^ 40 * 706696 * 2
def baseEnd_706696 : Nat := 53759218460721819607403

theorem tailTrace_706696 : CollatzResearch.WordTrace tailWord_706696 prefixEnd_706696 53759218460721819607403 := by
  unfold tailWord_706696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887660323884280456481971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17183547098512373941975961 12887660323884280456481971)
  ·
    refine ⟨19331490485826420684722957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12887660323884280456481971 19331490485826420684722957)
    ·
      refine ⟨7249308932184907756771109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19331490485826420684722957 7249308932184907756771109)
      ·
        refine ⟨1359245424784670204394583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7249308932184907756771109 1359245424784670204394583)
        ·
          refine ⟨2038868137177005306591875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359245424784670204394583 2038868137177005306591875)
          ·
            refine ⟨3058302205765507959887813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038868137177005306591875 3058302205765507959887813)
            ·
              refine ⟨573431663581032742478965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3058302205765507959887813 573431663581032742478965)
              ·
                refine ⟨53759218460721819607403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 573431663581032742478965 53759218460721819607403)
                ·
                  rfl

theorem cell21_706696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_706696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706696 prefixEnd_706696 := by exact prefixLift 706696
  have htrace : WordTrace (prefixWord ++ tailWord_706696) baseStart_706696 baseEnd_706696 := by
    simpa [prefixWord, tailWord_706696, baseEnd_706696] using wordTrace_append hprefix tailTrace_706696
  have hstable : (prefixWord ++ tailWord_706696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706696).length < 2 ^ (prefixWord ++ tailWord_706696).sum := by decide
  have hdescent : baseEnd_706696 < baseStart_706696 := by decide
  rcases family_descends (prefixWord ++ tailWord_706696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706820 : List Nat := [2, 3, 2, 2, 3, 1, 2, 3, 3]
def baseStart_706820 : Nat := 118140960795 + 706820 * 2 ^ 59
def prefixEnd_706820 : Nat := 4983230072969 + 3 ^ 40 * 706820 * 2
def baseEnd_706820 : Nat := 161305953871568798755289

theorem tailTrace_706820 : CollatzResearch.WordTrace tailWord_706820 prefixEnd_706820 161305953871568798755289 := by
  unfold tailWord_706820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12889921649659665045238957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17186562199546220060318609 12889921649659665045238957)
  ·
    refine ⟨4833720618622374391964609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12889921649659665045238957 4833720618622374391964609)
    ·
      refine ⟨3625290463966780793973457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4833720618622374391964609 3625290463966780793973457)
      ·
        refine ⟨2718967847975085595480093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3625290463966780793973457 2718967847975085595480093)
        ·
          refine ⟨1019612942990657098305035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2718967847975085595480093 1019612942990657098305035)
          ·
            refine ⟨1529419414485985647457553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019612942990657098305035 1529419414485985647457553)
            ·
              refine ⟨1147064560864489235593165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529419414485985647457553 1147064560864489235593165)
              ·
                refine ⟨430149210324183463347437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147064560864489235593165 430149210324183463347437)
                ·
                  refine ⟨161305953871568798755289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430149210324183463347437 161305953871568798755289)
                  ·
                    rfl

theorem cell21_706820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_706820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706820 prefixEnd_706820 := by exact prefixLift 706820
  have htrace : WordTrace (prefixWord ++ tailWord_706820) baseStart_706820 baseEnd_706820 := by
    simpa [prefixWord, tailWord_706820, baseEnd_706820] using wordTrace_append hprefix tailTrace_706820
  have hstable : (prefixWord ++ tailWord_706820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706820).length < 2 ^ (prefixWord ++ tailWord_706820).sum := by decide
  have hdescent : baseEnd_706820 < baseStart_706820 := by decide
  rcases family_descends (prefixWord ++ tailWord_706820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706865 : List Nat := [1, 2, 2, 3, 5, 1, 2, 5]
def baseStart_706865 : Nat := 118140960795 + 706865 * 2 ^ 59
def prefixEnd_706865 : Nat := 4983230072969 + 3 ^ 40 * 706865 * 2
def baseEnd_706865 : Nat := 53772074494886240168399

theorem tailTrace_706865 : CollatzResearch.WordTrace tailWord_706865 prefixEnd_706865 53772074494886240168399 := by
  unfold tailWord_706865
  simp only [CollatzResearch.WordTrace]
  refine ⟨25781484584156302775866049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17187656389437535183910699 25781484584156302775866049)
  ·
    refine ⟨19336113438117227081899537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25781484584156302775866049 19336113438117227081899537)
    ·
      refine ⟨14502085078587920311424653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19336113438117227081899537 14502085078587920311424653)
      ·
        refine ⟨5438281904470470116784245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14502085078587920311424653 5438281904470470116784245)
        ·
          refine ⟨509838928544106573448523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5438281904470470116784245 509838928544106573448523)
          ·
            refine ⟨764758392816159860172785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509838928544106573448523 764758392816159860172785)
            ·
              refine ⟨573568794612119895129589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 764758392816159860172785 573568794612119895129589)
              ·
                refine ⟨53772074494886240168399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 573568794612119895129589 53772074494886240168399)
                ·
                  rfl

theorem cell21_706865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 5].length) (baseStart_706865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706865 prefixEnd_706865 := by exact prefixLift 706865
  have htrace : WordTrace (prefixWord ++ tailWord_706865) baseStart_706865 baseEnd_706865 := by
    simpa [prefixWord, tailWord_706865, baseEnd_706865] using wordTrace_append hprefix tailTrace_706865
  have hstable : (prefixWord ++ tailWord_706865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706865).length < 2 ^ (prefixWord ++ tailWord_706865).sum := by decide
  have hdescent : baseEnd_706865 < baseStart_706865 := by decide
  rcases family_descends (prefixWord ++ tailWord_706865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706935 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 6]
def baseStart_706935 : Nat := 118140960795 + 706935 * 2 ^ 59
def prefixEnd_706935 : Nat := 4983230072969 + 3 ^ 40 * 706935 * 2
def baseEnd_706935 : Nat := 161332198438354154338387

theorem tailTrace_706935 : CollatzResearch.WordTrace tailWord_706935 prefixEnd_706935 161332198438354154338387 := by
  unfold tailWord_706935
  simp only [CollatzResearch.WordTrace]
  refine ⟨25784037693902704730914259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17189358462601803153942839 25784037693902704730914259)
  ·
    refine ⟨38676056540854057096371389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25784037693902704730914259 38676056540854057096371389)
    ·
      refine ⟨14503521202820271411139271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38676056540854057096371389 14503521202820271411139271)
      ·
        refine ⟨21755281804230407116708907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14503521202820271411139271 21755281804230407116708907)
        ·
          refine ⟨32632922706345610675063361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21755281804230407116708907 32632922706345610675063361)
          ·
            refine ⟨24474692029759208006297521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32632922706345610675063361 24474692029759208006297521)
            ·
              refine ⟨18356019022319406004723141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24474692029759208006297521 18356019022319406004723141)
              ·
                refine ⟨3441753566684888625885589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18356019022319406004723141 3441753566684888625885589)
                ·
                  refine ⟨161332198438354154338387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3441753566684888625885589 161332198438354154338387)
                  ·
                    rfl

theorem cell21_706935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_706935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706935 prefixEnd_706935 := by exact prefixLift 706935
  have htrace : WordTrace (prefixWord ++ tailWord_706935) baseStart_706935 baseEnd_706935 := by
    simpa [prefixWord, tailWord_706935, baseEnd_706935] using wordTrace_append hprefix tailTrace_706935
  have hstable : (prefixWord ++ tailWord_706935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706935).length < 2 ^ (prefixWord ++ tailWord_706935).sum := by decide
  have hdescent : baseEnd_706935 < baseStart_706935 := by decide
  rcases family_descends (prefixWord ++ tailWord_706935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706955 : List Nat := [1, 1, 1, 1, 4, 4, 4, 2, 3]
def baseStart_706955 : Nat := 118140960795 + 706955 * 2 ^ 59
def prefixEnd_706955 : Nat := 4983230072969 + 3 ^ 40 * 706955 * 2
def baseEnd_706955 : Nat := 161336762710838564005013

theorem tailTrace_706955 : CollatzResearch.WordTrace tailWord_706955 prefixEnd_706955 161336762710838564005013 := by
  unfold tailWord_706955
  simp only [CollatzResearch.WordTrace]
  refine ⟨25784767153830248146642319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17189844769220165431094879 25784767153830248146642319)
  ·
    refine ⟨38677150730745372219963479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25784767153830248146642319 38677150730745372219963479)
    ·
      refine ⟨58015726096118058329945219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38677150730745372219963479 58015726096118058329945219)
      ·
        refine ⟨87023589144177087494917829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58015726096118058329945219 87023589144177087494917829)
        ·
          refine ⟨16316922964533203905297093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87023589144177087494917829 16316922964533203905297093)
          ·
            refine ⟨3059423055849975732243205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16316922964533203905297093 3059423055849975732243205)
            ·
              refine ⟨573641822971870449795601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3059423055849975732243205 573641822971870449795601)
              ·
                refine ⟨430231367228902837346701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573641822971870449795601 430231367228902837346701)
                ·
                  refine ⟨161336762710838564005013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430231367228902837346701 161336762710838564005013)
                  ·
                    rfl

theorem cell21_706955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 3].length) (baseStart_706955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_706955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_706955 prefixEnd_706955 := by exact prefixLift 706955
  have htrace : WordTrace (prefixWord ++ tailWord_706955) baseStart_706955 baseEnd_706955 := by
    simpa [prefixWord, tailWord_706955, baseEnd_706955] using wordTrace_append hprefix tailTrace_706955
  have hstable : (prefixWord ++ tailWord_706955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706955).length < 2 ^ (prefixWord ++ tailWord_706955).sum := by decide
  have hdescent : baseEnd_706955 < baseStart_706955 := by decide
  rcases family_descends (prefixWord ++ tailWord_706955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707079 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 4]
def baseStart_707079 : Nat := 118140960795 + 707079 * 2 ^ 59
def prefixEnd_707079 : Nat := 4983230072969 + 3 ^ 40 * 707079 * 2
def baseEnd_707079 : Nat := 161365061200241903938093

theorem tailTrace_707079 : CollatzResearch.WordTrace tailWord_707079 prefixEnd_707079 161365061200241903938093 := by
  unfold tailWord_707079
  simp only [CollatzResearch.WordTrace]
  refine ⟨25789289805381017324156291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17192859870254011549437527 25789289805381017324156291)
  ·
    refine ⟨38683934708071525986234437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25789289805381017324156291 38683934708071525986234437)
    ·
      refine ⟨7253237757763411122418957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38683934708071525986234437 7253237757763411122418957)
      ·
        refine ⟨2719964159161279170907109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7253237757763411122418957 2719964159161279170907109)
        ·
          refine ⟨509993279842739844545083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2719964159161279170907109 509993279842739844545083)
          ·
            refine ⟨764989919764109766817625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509993279842739844545083 764989919764109766817625)
            ·
              refine ⟨573742439823082325113219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 764989919764109766817625 573742439823082325113219)
              ·
                refine ⟨860613659734623487669829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573742439823082325113219 860613659734623487669829)
                ·
                  refine ⟨161365061200241903938093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 860613659734623487669829 161365061200241903938093)
                  ·
                    rfl

theorem cell21_707079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 4].length) (baseStart_707079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707079 prefixEnd_707079 := by exact prefixLift 707079
  have htrace : WordTrace (prefixWord ++ tailWord_707079) baseStart_707079 baseEnd_707079 := by
    simpa [prefixWord, tailWord_707079, baseEnd_707079] using wordTrace_append hprefix tailTrace_707079
  have hstable : (prefixWord ++ tailWord_707079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707079).length < 2 ^ (prefixWord ++ tailWord_707079).sum := by decide
  have hdescent : baseEnd_707079 < baseStart_707079 := by decide
  rcases family_descends (prefixWord ++ tailWord_707079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707118 : List Nat := [4, 1, 3, 1, 12]
def baseStart_707118 : Nat := 118140960795 + 707118 * 2 ^ 59
def prefixEnd_707118 : Nat := 4983230072969 + 3 ^ 40 * 707118 * 2
def baseEnd_707118 : Nat := 1992271130019586454173

theorem tailTrace_707118 : CollatzResearch.WordTrace tailWord_707118 prefixEnd_707118 1992271130019586454173 := by
  unfold tailWord_707118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223839031529965873103251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17193808168159817989884005 3223839031529965873103251)
  ·
    refine ⟨4835758547294948809654877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3223839031529965873103251 4835758547294948809654877)
    ·
      refine ⟨1813409455235605803620579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4835758547294948809654877 1813409455235605803620579)
      ·
        refine ⟨2720114182853408705430869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1813409455235605803620579 2720114182853408705430869)
        ·
          refine ⟨1992271130019586454173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2720114182853408705430869 1992271130019586454173)
          ·
            rfl

theorem cell21_707118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 12].length) (baseStart_707118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707118 prefixEnd_707118 := by exact prefixLift 707118
  have htrace : WordTrace (prefixWord ++ tailWord_707118) baseStart_707118 baseEnd_707118 := by
    simpa [prefixWord, tailWord_707118, baseEnd_707118] using wordTrace_append hprefix tailTrace_707118
  have hstable : (prefixWord ++ tailWord_707118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707118).length < 2 ^ (prefixWord ++ tailWord_707118).sum := by decide
  have hdescent : baseEnd_707118 < baseStart_707118 := by decide
  rcases family_descends (prefixWord ++ tailWord_707118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707180 : List Nat := [2, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_707180 : Nat := 118140960795 + 707180 * 2 ^ 59
def prefixEnd_707180 : Nat := 4983230072969 + 3 ^ 40 * 707180 * 2
def baseEnd_707180 : Nat := 161388110776288172754553

theorem tailTrace_707180 : CollatzResearch.WordTrace tailWord_707180 prefixEnd_707180 161388110776288172754553 := by
  unfold tailWord_707180
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896486789007555786791497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17195315718676741049055329 12896486789007555786791497)
  ·
    refine ⟨9672365091755666840093623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12896486789007555786791497 9672365091755666840093623)
    ·
      refine ⟨14508547637633500260140435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9672365091755666840093623 14508547637633500260140435)
      ·
        refine ⟨21762821456450250390210653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14508547637633500260140435 21762821456450250390210653)
        ·
          refine ⟨8161058046168843896328995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21762821456450250390210653 8161058046168843896328995)
          ·
            refine ⟨12241587069253265844493493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161058046168843896328995 12241587069253265844493493)
            ·
              refine ⟨1147648787742493672921265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12241587069253265844493493 1147648787742493672921265)
              ·
                refine ⟨860736590806870254690949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147648787742493672921265 860736590806870254690949)
                ·
                  refine ⟨161388110776288172754553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 860736590806870254690949 161388110776288172754553)
                  ·
                    rfl

theorem cell21_707180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_707180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707180 prefixEnd_707180 := by exact prefixLift 707180
  have htrace : WordTrace (prefixWord ++ tailWord_707180) baseStart_707180 baseEnd_707180 := by
    simpa [prefixWord, tailWord_707180, baseEnd_707180] using wordTrace_append hprefix tailTrace_707180
  have hstable : (prefixWord ++ tailWord_707180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707180).length < 2 ^ (prefixWord ++ tailWord_707180).sum := by decide
  have hdescent : baseEnd_707180 < baseStart_707180 := by decide
  rcases family_descends (prefixWord ++ tailWord_707180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707304 : List Nat := [2, 1, 4, 1, 5, 1, 1, 6]
def baseStart_707304 : Nat := 118140960795 + 707304 * 2 ^ 59
def prefixEnd_707304 : Nat := 4983230072969 + 3 ^ 40 * 707304 * 2
def baseEnd_707304 : Nat := 53805469755230504229211

theorem tailTrace_707304 : CollatzResearch.WordTrace tailWord_707304 prefixEnd_707304 53805469755230504229211 := by
  unfold tailWord_707304
  simp only [CollatzResearch.WordTrace]
  refine ⟨12898748114782940375548483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17198330819710587167397977 12898748114782940375548483)
  ·
    refine ⟨19348122172174410563322725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12898748114782940375548483 19348122172174410563322725)
    ·
      refine ⟨3627772907282701980623011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19348122172174410563322725 3627772907282701980623011)
      ·
        refine ⟨5441659360924052970934517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627772907282701980623011 5441659360924052970934517)
        ·
          refine ⟨510155565086629966025111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5441659360924052970934517 510155565086629966025111)
          ·
            refine ⟨765233347629944949037667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510155565086629966025111 765233347629944949037667)
            ·
              refine ⟨1147850021444917423556501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765233347629944949037667 1147850021444917423556501)
              ·
                refine ⟨53805469755230504229211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1147850021444917423556501 53805469755230504229211)
                ·
                  rfl

theorem cell21_707304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_707304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707304 prefixEnd_707304 := by exact prefixLift 707304
  have htrace : WordTrace (prefixWord ++ tailWord_707304) baseStart_707304 baseEnd_707304 := by
    simpa [prefixWord, tailWord_707304, baseEnd_707304] using wordTrace_append hprefix tailTrace_707304
  have hstable : (prefixWord ++ tailWord_707304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707304).length < 2 ^ (prefixWord ++ tailWord_707304).sum := by decide
  have hdescent : baseEnd_707304 < baseStart_707304 := by decide
  rcases family_descends (prefixWord ++ tailWord_707304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707335 : List Nat := [1, 1, 4, 4, 1, 2, 2, 3, 3]
def baseStart_707335 : Nat := 118140960795 + 707335 * 2 ^ 59
def prefixEnd_707335 : Nat := 4983230072969 + 3 ^ 40 * 707335 * 2
def baseEnd_707335 : Nat := 161423483888042347670903

theorem tailTrace_707335 : CollatzResearch.WordTrace tailWord_707335 prefixEnd_707335 161423483888042347670903 := by
  unfold tailWord_707335
  simp only [CollatzResearch.WordTrace]
  refine ⟨25798626892453573045475459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17199084594969048696983639 25798626892453573045475459)
  ·
    refine ⟨38697940338680359568213189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25798626892453573045475459 38697940338680359568213189)
    ·
      refine ⟨7255863813502567419039973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38697940338680359568213189 7255863813502567419039973)
      ·
        refine ⟨1360474465031731391069995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7255863813502567419039973 1360474465031731391069995)
        ·
          refine ⟨2040711697547597086604993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360474465031731391069995 2040711697547597086604993)
          ·
            refine ⟨1530533773160697814953745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2040711697547597086604993 1530533773160697814953745)
            ·
              refine ⟨1147900329870523361215309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530533773160697814953745 1147900329870523361215309)
              ·
                refine ⟨430462623701446260455741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147900329870523361215309 430462623701446260455741)
                ·
                  refine ⟨161423483888042347670903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430462623701446260455741 161423483888042347670903)
                  ·
                    rfl

theorem cell21_707335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 3].length) (baseStart_707335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707335 prefixEnd_707335 := by exact prefixLift 707335
  have htrace : WordTrace (prefixWord ++ tailWord_707335) baseStart_707335 baseEnd_707335 := by
    simpa [prefixWord, tailWord_707335, baseEnd_707335] using wordTrace_append hprefix tailTrace_707335
  have hstable : (prefixWord ++ tailWord_707335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707335).length < 2 ^ (prefixWord ++ tailWord_707335).sum := by decide
  have hdescent : baseEnd_707335 < baseStart_707335 := by decide
  rcases family_descends (prefixWord ++ tailWord_707335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707391 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 6]
def baseStart_707391 : Nat := 118140960795 + 707391 * 2 ^ 59
def prefixEnd_707391 : Nat := 4983230072969 + 3 ^ 40 * 707391 * 2
def baseEnd_707391 : Nat := 161436263850998694737455

theorem tailTrace_707391 : CollatzResearch.WordTrace tailWord_707391 prefixEnd_707391 161436263850998694737455 := by
  unfold tailWord_707391
  simp only [CollatzResearch.WordTrace]
  refine ⟨25800669380250694609514027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17200446253500463073009351 25800669380250694609514027)
  ·
    refine ⟨38701004070376041914271041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25800669380250694609514027 38701004070376041914271041)
    ·
      refine ⟨29025753052782031435703281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38701004070376041914271041 29025753052782031435703281)
      ·
        refine ⟨21769314789586523576777461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29025753052782031435703281 21769314789586523576777461)
        ·
          refine ⟨2040873261523736585322887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21769314789586523576777461 2040873261523736585322887)
          ·
            refine ⟨3061309892285604877984331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040873261523736585322887 3061309892285604877984331)
            ·
              refine ⟨4591964838428407316976497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061309892285604877984331 4591964838428407316976497)
              ·
                refine ⟨3443973628821305487732373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4591964838428407316976497 3443973628821305487732373)
                ·
                  refine ⟨161436263850998694737455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3443973628821305487732373 161436263850998694737455)
                  ·
                    rfl

theorem cell21_707391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_707391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707391 prefixEnd_707391 := by exact prefixLift 707391
  have htrace : WordTrace (prefixWord ++ tailWord_707391) baseStart_707391 baseEnd_707391 := by
    simpa [prefixWord, tailWord_707391, baseEnd_707391] using wordTrace_append hprefix tailTrace_707391
  have hstable : (prefixWord ++ tailWord_707391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707391).length < 2 ^ (prefixWord ++ tailWord_707391).sum := by decide
  have hdescent : baseEnd_707391 < baseStart_707391 := by decide
  rcases family_descends (prefixWord ++ tailWord_707391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707436 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_707436 : Nat := 118140960795 + 707436 * 2 ^ 59
def prefixEnd_707436 : Nat := 4983230072969 + 3 ^ 40 * 707436 * 2
def baseEnd_707436 : Nat := 161446533464088616487363

theorem tailTrace_707436 : CollatzResearch.WordTrace tailWord_707436 prefixEnd_707436 161446533464088616487363 := by
  unfold tailWord_707436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901155332543833647451081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17201540443391778196601441 12901155332543833647451081)
  ·
    refine ⟨9675866499407875235588311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12901155332543833647451081 9675866499407875235588311)
    ·
      refine ⟨14513799749111812853382467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9675866499407875235588311 14513799749111812853382467)
      ·
        refine ⟨21770699623667719280073701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14513799749111812853382467 21770699623667719280073701)
        ·
          refine ⟨4082006179437697365013819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21770699623667719280073701 4082006179437697365013819)
          ·
            refine ⟨6123009269156546047520729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082006179437697365013819 6123009269156546047520729)
            ·
              refine ⟨4592256951867409535640547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6123009269156546047520729 4592256951867409535640547)
              ·
                refine ⟨6888385427801114303460821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592256951867409535640547 6888385427801114303460821)
                ·
                  refine ⟨161446533464088616487363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6888385427801114303460821 161446533464088616487363)
                  ·
                    rfl

theorem cell21_707436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_707436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707436 prefixEnd_707436 := by exact prefixLift 707436
  have htrace : WordTrace (prefixWord ++ tailWord_707436) baseStart_707436 baseEnd_707436 := by
    simpa [prefixWord, tailWord_707436, baseEnd_707436] using wordTrace_append hprefix tailTrace_707436
  have hstable : (prefixWord ++ tailWord_707436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707436).length < 2 ^ (prefixWord ++ tailWord_707436).sum := by decide
  have hdescent : baseEnd_707436 < baseStart_707436 := by decide
  rcases family_descends (prefixWord ++ tailWord_707436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707467 : List Nat := [1, 1, 1, 1, 4, 2, 3, 4, 4]
def baseStart_707467 : Nat := 118140960795 + 707467 * 2 ^ 59
def prefixEnd_707467 : Nat := 4983230072969 + 3 ^ 40 * 707467 * 2
def baseEnd_707467 : Nat := 161453608086439451470633

theorem tailTrace_707467 : CollatzResearch.WordTrace tailWord_707467 prefixEnd_707467 161453608086439451470633 := by
  unfold tailWord_707467
  simp only [CollatzResearch.WordTrace]
  refine ⟨25803441327975359589280655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17202294218650239726187103 25803441327975359589280655)
  ·
    refine ⟨38705161991963039383920983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25803441327975359589280655 38705161991963039383920983)
    ·
      refine ⟨58057742987944559075881475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38705161991963039383920983 58057742987944559075881475)
      ·
        refine ⟨87086614481916838613822213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58057742987944559075881475 87086614481916838613822213)
        ·
          refine ⟨16328740215359407240091665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87086614481916838613822213 16328740215359407240091665)
          ·
            refine ⟨12246555161519555430068749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16328740215359407240091665 12246555161519555430068749)
            ·
              refine ⟨4592458185569833286275781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12246555161519555430068749 4592458185569833286275781)
              ·
                refine ⟨861085909794343741176709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4592458185569833286275781 861085909794343741176709)
                ·
                  refine ⟨161453608086439451470633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861085909794343741176709 161453608086439451470633)
                  ·
                    rfl

theorem cell21_707467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 4].length) (baseStart_707467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707467 prefixEnd_707467 := by exact prefixLift 707467
  have htrace : WordTrace (prefixWord ++ tailWord_707467) baseStart_707467 baseEnd_707467 := by
    simpa [prefixWord, tailWord_707467, baseEnd_707467] using wordTrace_append hprefix tailTrace_707467
  have hstable : (prefixWord ++ tailWord_707467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707467).length < 2 ^ (prefixWord ++ tailWord_707467).sum := by decide
  have hdescent : baseEnd_707467 < baseStart_707467 := by decide
  rcases family_descends (prefixWord ++ tailWord_707467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707574 : List Nat := [5, 1, 1, 1, 3, 1, 9]
def baseStart_707574 : Nat := 118140960795 + 707574 * 2 ^ 59
def prefixEnd_707574 : Nat := 4983230072969 + 3 ^ 40 * 707574 * 2
def baseEnd_707574 : Nat := 17942002993803449243009

theorem tailTrace_707574 : CollatzResearch.WordTrace tailWord_707574 prefixEnd_707574 17942002993803449243009 := by
  unfold tailWord_707574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612958996161732303964111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17204895959058477908950517 1612958996161732303964111)
  ·
    refine ⟨2419438494242598455946167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612958996161732303964111 2419438494242598455946167)
    ·
      refine ⟨3629157741363897683919251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419438494242598455946167 3629157741363897683919251)
      ·
        refine ⟨5443736612045846525878877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3629157741363897683919251 5443736612045846525878877)
        ·
          refine ⟨2041401229517192447204579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5443736612045846525878877 2041401229517192447204579)
          ·
            refine ⟨3062101844275788670806869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041401229517192447204579 3062101844275788670806869)
            ·
              refine ⟨17942002993803449243009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3062101844275788670806869 17942002993803449243009)
              ·
                rfl

theorem cell21_707574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 9].length) (baseStart_707574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707574 prefixEnd_707574 := by exact prefixLift 707574
  have htrace : WordTrace (prefixWord ++ tailWord_707574) baseStart_707574 baseEnd_707574 := by
    simpa [prefixWord, tailWord_707574, baseEnd_707574] using wordTrace_append hprefix tailTrace_707574
  have hstable : (prefixWord ++ tailWord_707574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707574).length < 2 ^ (prefixWord ++ tailWord_707574).sum := by decide
  have hdescent : baseEnd_707574 < baseStart_707574 := by decide
  rcases family_descends (prefixWord ++ tailWord_707574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707681 : List Nat := [1, 2, 3, 1, 1, 2, 3, 5, 3]
def baseStart_707681 : Nat := 118140960795 + 707681 * 2 ^ 59
def prefixEnd_707681 : Nat := 4983230072969 + 3 ^ 40 * 707681 * 2
def baseEnd_707681 : Nat := 161502445802022634903529

theorem tailTrace_707681 : CollatzResearch.WordTrace tailWord_707681 prefixEnd_707681 161502445802022634903529 := by
  unfold tailWord_707681
  simp only [CollatzResearch.WordTrace]
  refine ⟨25811246549200074137570897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17207497699466716091713931 25811246549200074137570897)
  ·
    refine ⟨19358434911900055603178173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25811246549200074137570897 19358434911900055603178173)
    ·
      refine ⟨7259413091962520851191815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19358434911900055603178173 7259413091962520851191815)
      ·
        refine ⟨10889119637943781276787723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259413091962520851191815 10889119637943781276787723)
        ·
          refine ⟨16333679456915671915181585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10889119637943781276787723 16333679456915671915181585)
          ·
            refine ⟨12250259592686753936386189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16333679456915671915181585 12250259592686753936386189)
            ·
              refine ⟨4593847347257532726144821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12250259592686753936386189 4593847347257532726144821)
              ·
                refine ⟨430673188805393693076077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4593847347257532726144821 430673188805393693076077)
                ·
                  refine ⟨161502445802022634903529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430673188805393693076077 161502445802022634903529)
                  ·
                    rfl

theorem cell21_707681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_707681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707681 prefixEnd_707681 := by exact prefixLift 707681
  have htrace : WordTrace (prefixWord ++ tailWord_707681) baseStart_707681 baseEnd_707681 := by
    simpa [prefixWord, tailWord_707681, baseEnd_707681] using wordTrace_append hprefix tailTrace_707681
  have hstable : (prefixWord ++ tailWord_707681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707681).length < 2 ^ (prefixWord ++ tailWord_707681).sum := by decide
  have hdescent : baseEnd_707681 < baseStart_707681 := by decide
  rcases family_descends (prefixWord ++ tailWord_707681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707709 : List Nat := [1, 4, 1, 1, 3, 1, 2, 8]
def baseStart_707709 : Nat := 118140960795 + 707709 * 2 ^ 59
def prefixEnd_707709 : Nat := 4983230072969 + 3 ^ 40 * 707709 * 2
def baseEnd_707709 : Nat := 53836278594500269478935

theorem tailTrace_707709 : CollatzResearch.WordTrace tailWord_707709 prefixEnd_707709 53836278594500269478935 := by
  unfold tailWord_707709
  simp only [CollatzResearch.WordTrace]
  refine ⟨25812267793098634919590181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17208178528732423279726787 25812267793098634919590181)
  ·
    refine ⟨4839800211205994047423159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25812267793098634919590181 4839800211205994047423159)
    ·
      refine ⟨7259700316808991071134739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4839800211205994047423159 7259700316808991071134739)
      ·
        refine ⟨10889550475213486606702109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259700316808991071134739 10889550475213486606702109)
        ·
          refine ⟨4083581428205057477513291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10889550475213486606702109 4083581428205057477513291)
          ·
            refine ⟨6125372142307586216269937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4083581428205057477513291 6125372142307586216269937)
            ·
              refine ⟨4594029106730689662202453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6125372142307586216269937 4594029106730689662202453)
              ·
                refine ⟨53836278594500269478935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4594029106730689662202453 53836278594500269478935)
                ·
                  rfl

theorem cell21_707709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 8].length) (baseStart_707709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707709 prefixEnd_707709 := by exact prefixLift 707709
  have htrace : WordTrace (prefixWord ++ tailWord_707709) baseStart_707709 baseEnd_707709 := by
    simpa [prefixWord, tailWord_707709, baseEnd_707709] using wordTrace_append hprefix tailTrace_707709
  have hstable : (prefixWord ++ tailWord_707709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707709).length < 2 ^ (prefixWord ++ tailWord_707709).sum := by decide
  have hdescent : baseEnd_707709 < baseStart_707709 := by decide
  rcases family_descends (prefixWord ++ tailWord_707709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707726 : List Nat := [4, 1, 1, 3, 2, 2, 1, 7]
def baseStart_707726 : Nat := 118140960795 + 707726 * 2 ^ 59
def prefixEnd_707726 : Nat := 4983230072969 + 3 ^ 40 * 707726 * 2
def baseEnd_707726 : Nat := 53837571805037518884479

theorem tailTrace_707726 : CollatzResearch.WordTrace tailWord_707726 prefixEnd_707726 53837571805037518884479 := by
  unfold tailWord_707726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3226610979254630852869879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17208591889358031215306021 3226610979254630852869879)
  ·
    refine ⟨4839916468881946279304819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3226610979254630852869879 4839916468881946279304819)
    ·
      refine ⟨7259874703322919418957229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4839916468881946279304819 7259874703322919418957229)
      ·
        refine ⟨2722453013746094782108961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7259874703322919418957229 2722453013746094782108961)
        ·
          refine ⟨2041839760309571086581721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2722453013746094782108961 2041839760309571086581721)
          ·
            refine ⟨1531379820232178314936291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041839760309571086581721 1531379820232178314936291)
            ·
              refine ⟨2297069730348267472404437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531379820232178314936291 2297069730348267472404437)
              ·
                refine ⟨53837571805037518884479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2297069730348267472404437 53837571805037518884479)
                ·
                  rfl

theorem cell21_707726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_707726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707726 prefixEnd_707726 := by exact prefixLift 707726
  have htrace : WordTrace (prefixWord ++ tailWord_707726) baseStart_707726 baseEnd_707726 := by
    simpa [prefixWord, tailWord_707726, baseEnd_707726] using wordTrace_append hprefix tailTrace_707726
  have hstable : (prefixWord ++ tailWord_707726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707726).length < 2 ^ (prefixWord ++ tailWord_707726).sum := by decide
  have hdescent : baseEnd_707726 < baseStart_707726 := by decide
  rcases family_descends (prefixWord ++ tailWord_707726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707743 : List Nat := [1, 1, 2, 6, 3, 1, 7]
def baseStart_707743 : Nat := 118140960795 + 707743 * 2 ^ 59
def prefixEnd_707743 : Nat := 4983230072969 + 3 ^ 40 * 707743 * 2
def baseEnd_707743 : Nat := 17946288338524922763341

theorem tailTrace_707743 : CollatzResearch.WordTrace tailWord_707743 prefixEnd_707743 17946288338524922763341 := by
  unfold tailWord_707743
  simp only [CollatzResearch.WordTrace]
  refine ⟨25813507874975458726327883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17209005249983639150885255 25813507874975458726327883)
  ·
    refine ⟨38720261812463188089491825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25813507874975458726327883 38720261812463188089491825)
    ·
      refine ⟨29040196359347391067118869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38720261812463188089491825 29040196359347391067118869)
      ·
        refine ⟨1361259204344408956271197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29040196359347391067118869 1361259204344408956271197)
        ·
          refine ⟨510472201629153358601699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1361259204344408956271197 510472201629153358601699)
          ·
            refine ⟨765708302443730037902549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510472201629153358601699 765708302443730037902549)
            ·
              refine ⟨17946288338524922763341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 765708302443730037902549 17946288338524922763341)
              ·
                rfl

theorem cell21_707743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 7].length) (baseStart_707743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707743 prefixEnd_707743 := by exact prefixLift 707743
  have htrace : WordTrace (prefixWord ++ tailWord_707743) baseStart_707743 baseEnd_707743 := by
    simpa [prefixWord, tailWord_707743, baseEnd_707743] using wordTrace_append hprefix tailTrace_707743
  have hstable : (prefixWord ++ tailWord_707743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707743).length < 2 ^ (prefixWord ++ tailWord_707743).sum := by decide
  have hdescent : baseEnd_707743 < baseStart_707743 := by decide
  rcases family_descends (prefixWord ++ tailWord_707743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707805 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 4]
def baseStart_707805 : Nat := 118140960795 + 707805 * 2 ^ 59
def prefixEnd_707805 : Nat := 4983230072969 + 3 ^ 40 * 707805 * 2
def baseEnd_707805 : Nat := 161530744291425974836609

theorem tailTrace_707805 : CollatzResearch.WordTrace tailWord_707805 prefixEnd_707805 161530744291425974836609 := by
  unfold tailWord_707805
  simp only [CollatzResearch.WordTrace]
  refine ⟨25815769200750843315084869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17210512800500562210056579 25815769200750843315084869)
  ·
    refine ⟨4840456725140783121578413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25815769200750843315084869 4840456725140783121578413)
    ·
      refine ⟨1815171271927793670591905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4840456725140783121578413 1815171271927793670591905)
      ·
        refine ⟨1361378453945845252943929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815171271927793670591905 1361378453945845252943929)
        ·
          refine ⟨1021033840459383939707947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1361378453945845252943929 1021033840459383939707947)
          ·
            refine ⟨1531550760689075909561921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021033840459383939707947 1531550760689075909561921)
            ·
              refine ⟨1148663070516806932171441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531550760689075909561921 1148663070516806932171441)
              ·
                refine ⟨861497302887605199128581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148663070516806932171441 861497302887605199128581)
                ·
                  refine ⟨161530744291425974836609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861497302887605199128581 161530744291425974836609)
                  ·
                    rfl

theorem cell21_707805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_707805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707805 prefixEnd_707805 := by exact prefixLift 707805
  have htrace : WordTrace (prefixWord ++ tailWord_707805) baseStart_707805 baseEnd_707805 := by
    simpa [prefixWord, tailWord_707805, baseEnd_707805] using wordTrace_append hprefix tailTrace_707805
  have hstable : (prefixWord ++ tailWord_707805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707805).length < 2 ^ (prefixWord ++ tailWord_707805).sum := by decide
  have hdescent : baseEnd_707805 < baseStart_707805 := by decide
  rcases family_descends (prefixWord ++ tailWord_707805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707816 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 5]
def baseStart_707816 : Nat := 118140960795 + 707816 * 2 ^ 59
def prefixEnd_707816 : Nat := 4983230072969 + 3 ^ 40 * 707816 * 2
def baseEnd_707816 : Nat := 161533254641292400153253

theorem tailTrace_707816 : CollatzResearch.WordTrace tailWord_707816 prefixEnd_707816 161533254641292400153253 := by
  unfold tailWord_707816
  simp only [CollatzResearch.WordTrace]
  refine ⟨12908085201855496096867651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17210780269140661462490201 12908085201855496096867651)
  ·
    refine ⟨19362127802783244145301477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12908085201855496096867651 19362127802783244145301477)
    ·
      refine ⟨3630398963021858277244027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19362127802783244145301477 3630398963021858277244027)
      ·
        refine ⟨5445598444532787415866041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630398963021858277244027 5445598444532787415866041)
        ·
          refine ⟨4084198833399590561899531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5445598444532787415866041 4084198833399590561899531)
          ·
            refine ⟨6126298250099385842849297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084198833399590561899531 6126298250099385842849297)
            ·
              refine ⟨4594723687574539382136973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6126298250099385842849297 4594723687574539382136973)
              ·
                refine ⟨1723021382840452268301365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4594723687574539382136973 1723021382840452268301365)
                ·
                  refine ⟨161533254641292400153253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1723021382840452268301365 161533254641292400153253)
                  ·
                    rfl

theorem cell21_707816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_707816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707816 prefixEnd_707816 := by exact prefixLift 707816
  have htrace : WordTrace (prefixWord ++ tailWord_707816) baseStart_707816 baseEnd_707816 := by
    simpa [prefixWord, tailWord_707816, baseEnd_707816] using wordTrace_append hprefix tailTrace_707816
  have hstable : (prefixWord ++ tailWord_707816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707816).length < 2 ^ (prefixWord ++ tailWord_707816).sum := by decide
  have hdescent : baseEnd_707816 < baseStart_707816 := by decide
  rcases family_descends (prefixWord ++ tailWord_707816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707864 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_707864 : Nat := 118140960795 + 707864 * 2 ^ 59
def prefixEnd_707864 : Nat := 4983230072969 + 3 ^ 40 * 707864 * 2
def baseEnd_707864 : Nat := 161544208895254983353155

theorem tailTrace_707864 : CollatzResearch.WordTrace tailWord_707864 prefixEnd_707864 161544208895254983353155 := by
  unfold tailWord_707864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12908960553768548195741323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17211947405024730927655097 12908960553768548195741323)
  ·
    refine ⟨19363440830652822293611985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12908960553768548195741323 19363440830652822293611985)
    ·
      refine ⟨14522580622989616720208989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19363440830652822293611985 14522580622989616720208989)
      ·
        refine ⟨5445967733621106270078371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14522580622989616720208989 5445967733621106270078371)
        ·
          refine ⟨8168951600431659405117557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445967733621106270078371 8168951600431659405117557)
          ·
            refine ⟨765839212540468069229771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8168951600431659405117557 765839212540468069229771)
            ·
              refine ⟨1148758818810702103844657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765839212540468069229771 1148758818810702103844657)
              ·
                refine ⟨861569114108026577883493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148758818810702103844657 861569114108026577883493)
                ·
                  refine ⟨161544208895254983353155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861569114108026577883493 161544208895254983353155)
                  ·
                    rfl

theorem cell21_707864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_707864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707864 prefixEnd_707864 := by exact prefixLift 707864
  have htrace : WordTrace (prefixWord ++ tailWord_707864) baseStart_707864 baseEnd_707864 := by
    simpa [prefixWord, tailWord_707864, baseEnd_707864] using wordTrace_append hprefix tailTrace_707864
  have hstable : (prefixWord ++ tailWord_707864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707864).length < 2 ^ (prefixWord ++ tailWord_707864).sum := by decide
  have hdescent : baseEnd_707864 < baseStart_707864 := by decide
  rcases family_descends (prefixWord ++ tailWord_707864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707940 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_707940 : Nat := 118140960795 + 707940 * 2 ^ 59
def prefixEnd_707940 : Nat := 4983230072969 + 3 ^ 40 * 707940 * 2
def baseEnd_707940 : Nat := 161561553130695740086333

theorem tailTrace_707940 : CollatzResearch.WordTrace tailWord_707940 prefixEnd_707940 161561553130695740086333 := by
  unfold tailWord_707940
  simp only [CollatzResearch.WordTrace]
  refine ⟨12910346527630880685624637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17213795370174507580832849 12910346527630880685624637)
  ·
    refine ⟨4841379947861580257109239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12910346527630880685624637 4841379947861580257109239)
    ·
      refine ⟨7262069921792370385663859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4841379947861580257109239 7262069921792370385663859)
      ·
        refine ⟨10893104882688555578495789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7262069921792370385663859 10893104882688555578495789)
        ·
          refine ⟨4084914331008208341935921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10893104882688555578495789 4084914331008208341935921)
          ·
            refine ⟨3063685748256156256451941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4084914331008208341935921 3063685748256156256451941)
            ·
              refine ⟨574441077798029298084739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3063685748256156256451941 574441077798029298084739)
              ·
                refine ⟨861661616697043947127109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574441077798029298084739 861661616697043947127109)
                ·
                  refine ⟨161561553130695740086333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861661616697043947127109 161561553130695740086333)
                  ·
                    rfl

theorem cell21_707940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_707940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707940 prefixEnd_707940 := by exact prefixLift 707940
  have htrace : WordTrace (prefixWord ++ tailWord_707940) baseStart_707940 baseEnd_707940 := by
    simpa [prefixWord, tailWord_707940, baseEnd_707940] using wordTrace_append hprefix tailTrace_707940
  have hstable : (prefixWord ++ tailWord_707940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707940).length < 2 ^ (prefixWord ++ tailWord_707940).sum := by decide
  have hdescent : baseEnd_707940 < baseStart_707940 := by decide
  rcases family_descends (prefixWord ++ tailWord_707940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707951 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 7]
def baseStart_707951 : Nat := 118140960795 + 707951 * 2 ^ 59
def prefixEnd_707951 : Nat := 4983230072969 + 3 ^ 40 * 707951 * 2
def baseEnd_707951 : Nat := 161564063480562165402977

theorem tailTrace_707951 : CollatzResearch.WordTrace tailWord_707951 prefixEnd_707951 161564063480562165402977 := by
  unfold tailWord_707951
  simp only [CollatzResearch.WordTrace]
  refine ⟨25821094258221910249899707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17214062838814606833266471 25821094258221910249899707)
  ·
    refine ⟨38731641387332865374849561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25821094258221910249899707 38731641387332865374849561)
    ·
      refine ⟨29048731040499649031137171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38731641387332865374849561 29048731040499649031137171)
      ·
        refine ⟨43573096560749473546705757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29048731040499649031137171 43573096560749473546705757)
        ·
          refine ⟨16339911210281052580014659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43573096560749473546705757 16339911210281052580014659)
          ·
            refine ⟨24509866815421578870021989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16339911210281052580014659 24509866815421578870021989)
            ·
              refine ⟨4595600027891546038129123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24509866815421578870021989 4595600027891546038129123)
              ·
                refine ⟨6893400041837319057193685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595600027891546038129123 6893400041837319057193685)
                ·
                  refine ⟨161564063480562165402977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6893400041837319057193685 161564063480562165402977)
                  ·
                    rfl

theorem cell21_707951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_707951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707951 prefixEnd_707951 := by exact prefixLift 707951
  have htrace : WordTrace (prefixWord ++ tailWord_707951) baseStart_707951 baseEnd_707951 := by
    simpa [prefixWord, tailWord_707951, baseEnd_707951] using wordTrace_append hprefix tailTrace_707951
  have hstable : (prefixWord ++ tailWord_707951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707951).length < 2 ^ (prefixWord ++ tailWord_707951).sum := by decide
  have hdescent : baseEnd_707951 < baseStart_707951 := by decide
  rcases family_descends (prefixWord ++ tailWord_707951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707999 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 4]
def baseStart_707999 : Nat := 118140960795 + 707999 * 2 ^ 59
def prefixEnd_707999 : Nat := 4983230072969 + 3 ^ 40 * 707999 * 2
def baseEnd_707999 : Nat := 161575017734524748602879

theorem tailTrace_707999 : CollatzResearch.WordTrace tailWord_707999 prefixEnd_707999 161575017734524748602879 := by
  unfold tailWord_707999
  simp only [CollatzResearch.WordTrace]
  refine ⟨25822844962048014447647051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17215229974698676298431367 25822844962048014447647051)
  ·
    refine ⟨38734267443072021671470577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25822844962048014447647051 38734267443072021671470577)
    ·
      refine ⟨29050700582304016253602933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38734267443072021671470577 29050700582304016253602933)
      ·
        refine ⟨2723503179591001523775275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29050700582304016253602933 2723503179591001523775275)
        ·
          refine ⟨4085254769386502285662913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723503179591001523775275 4085254769386502285662913)
          ·
            refine ⟨3063941077039876714247185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4085254769386502285662913 3063941077039876714247185)
            ·
              refine ⟨2297955807779907535685389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3063941077039876714247185 2297955807779907535685389)
              ·
                refine ⟨861733427917465325882021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2297955807779907535685389 861733427917465325882021)
                ·
                  refine ⟨161575017734524748602879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861733427917465325882021 161575017734524748602879)
                  ·
                    rfl

theorem cell21_707999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 4].length) (baseStart_707999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_707999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_707999 prefixEnd_707999 := by exact prefixLift 707999
  have htrace : WordTrace (prefixWord ++ tailWord_707999) baseStart_707999 baseEnd_707999 := by
    simpa [prefixWord, tailWord_707999, baseEnd_707999] using wordTrace_append hprefix tailTrace_707999
  have hstable : (prefixWord ++ tailWord_707999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707999).length < 2 ^ (prefixWord ++ tailWord_707999).sum := by decide
  have hdescent : baseEnd_707999 < baseStart_707999 := by decide
  rcases family_descends (prefixWord ++ tailWord_707999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708044 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_708044 : Nat := 118140960795 + 708044 * 2 ^ 59
def prefixEnd_708044 : Nat := 4983230072969 + 3 ^ 40 * 708044 * 2
def baseEnd_708044 : Nat := 161585287347614670352787

theorem tailTrace_708044 : CollatzResearch.WordTrace tailWord_708044 prefixEnd_708044 161585287347614670352787 := by
  unfold tailWord_708044
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912243123442493566517593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17216324164589991422023457 12912243123442493566517593)
  ·
    refine ⟨9684182342581870174888195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12912243123442493566517593 9684182342581870174888195)
    ·
      refine ⟨14526273513872805262332293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9684182342581870174888195 14526273513872805262332293)
      ·
        refine ⟨2723676283851150986687305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14526273513872805262332293 2723676283851150986687305)
        ·
          refine ⟨2042757212888363240015479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2723676283851150986687305 2042757212888363240015479)
          ·
            refine ⟨3064135819332544860023219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042757212888363240015479 3064135819332544860023219)
            ·
              refine ⟨4596203728998817290034829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3064135819332544860023219 4596203728998817290034829)
              ·
                refine ⟨1723576398374556483763061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4596203728998817290034829 1723576398374556483763061)
                ·
                  refine ⟨161585287347614670352787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1723576398374556483763061 161585287347614670352787)
                  ·
                    rfl

theorem cell21_708044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_708044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708044 prefixEnd_708044 := by exact prefixLift 708044
  have htrace : WordTrace (prefixWord ++ tailWord_708044) baseStart_708044 baseEnd_708044 := by
    simpa [prefixWord, tailWord_708044, baseEnd_708044] using wordTrace_append hprefix tailTrace_708044
  have hstable : (prefixWord ++ tailWord_708044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708044).length < 2 ^ (prefixWord ++ tailWord_708044).sum := by decide
  have hdescent : baseEnd_708044 < baseStart_708044 := by decide
  rcases family_descends (prefixWord ++ tailWord_708044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708151 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 4]
def baseStart_708151 : Nat := 118140960795 + 708151 * 2 ^ 59
def prefixEnd_708151 : Nat := 4983230072969 + 3 ^ 40 * 708151 * 2
def baseEnd_708151 : Nat := 161609706205406262069235

theorem tailTrace_708151 : CollatzResearch.WordTrace tailWord_708151 prefixEnd_708151 161609706205406262069235 := by
  unfold tailWord_708151
  simp only [CollatzResearch.WordTrace]
  refine ⟨25828388857497344407180307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17218925904998229604786871 25828388857497344407180307)
  ·
    refine ⟨38742583286246016610770461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25828388857497344407180307 38742583286246016610770461)
    ·
      refine ⟨14528468732342256229038923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38742583286246016610770461 14528468732342256229038923)
      ·
        refine ⟨21792703098513384343558385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14528468732342256229038923 21792703098513384343558385)
        ·
          refine ⟨16344527323885038257668789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21792703098513384343558385 16344527323885038257668789)
          ·
            refine ⟨1532299436614222336656449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16344527323885038257668789 1532299436614222336656449)
            ·
              refine ⟨1149224577460666752492337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532299436614222336656449 1149224577460666752492337)
              ·
                refine ⟨861918433095500064369253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149224577460666752492337 861918433095500064369253)
                ·
                  refine ⟨161609706205406262069235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861918433095500064369253 161609706205406262069235)
                  ·
                    rfl

theorem cell21_708151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 4].length) (baseStart_708151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708151 prefixEnd_708151 := by exact prefixLift 708151
  have htrace : WordTrace (prefixWord ++ tailWord_708151) baseStart_708151 baseEnd_708151 := by
    simpa [prefixWord, tailWord_708151, baseEnd_708151] using wordTrace_append hprefix tailTrace_708151
  have hstable : (prefixWord ++ tailWord_708151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708151).length < 2 ^ (prefixWord ++ tailWord_708151).sum := by decide
  have hdescent : baseEnd_708151 < baseStart_708151 := by decide
  rcases family_descends (prefixWord ++ tailWord_708151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708213 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 5]
def baseStart_708213 : Nat := 118140960795 + 708213 * 2 ^ 59
def prefixEnd_708213 : Nat := 4983230072969 + 3 ^ 40 * 708213 * 2
def baseEnd_708213 : Nat := 161623855450107932035775

theorem tailTrace_708213 : CollatzResearch.WordTrace tailWord_708213 prefixEnd_708213 161623855450107932035775 := by
  unfold tailWord_708213
  simp only [CollatzResearch.WordTrace]
  refine ⟨25830650183272728995937293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17220433455515152663958195 25830650183272728995937293)
  ·
    refine ⟨9686493818727273373476485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25830650183272728995937293 9686493818727273373476485)
    ·
      refine ⟨1816217591011363757526841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9686493818727273373476485 1816217591011363757526841)
      ·
        refine ⟨1362163193258522818145131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1816217591011363757526841 1362163193258522818145131)
        ·
          refine ⟨2043244789887784227217697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362163193258522818145131 2043244789887784227217697)
          ·
            refine ⟨1532433592415838170413273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2043244789887784227217697 1532433592415838170413273)
            ·
              refine ⟨1149325194311878627809955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532433592415838170413273 1149325194311878627809955)
              ·
                refine ⟨1723987791467817941714933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149325194311878627809955 1723987791467817941714933)
                ·
                  refine ⟨161623855450107932035775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1723987791467817941714933 161623855450107932035775)
                  ·
                    rfl

theorem cell21_708213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_708213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708213 prefixEnd_708213 := by exact prefixLift 708213
  have htrace : WordTrace (prefixWord ++ tailWord_708213) baseStart_708213 baseEnd_708213 := by
    simpa [prefixWord, tailWord_708213, baseEnd_708213] using wordTrace_append hprefix tailTrace_708213
  have hstable : (prefixWord ++ tailWord_708213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708213).length < 2 ^ (prefixWord ++ tailWord_708213).sum := by decide
  have hdescent : baseEnd_708213 < baseStart_708213 := by decide
  rcases family_descends (prefixWord ++ tailWord_708213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708224 : List Nat := [2, 1, 1, 2, 1, 4, 2, 8]
def baseStart_708224 : Nat := 118140960795 + 708224 * 2 ^ 59
def prefixEnd_708224 : Nat := 4983230072969 + 3 ^ 40 * 708224 * 2
def baseEnd_708224 : Nat := 53875455266658119117473

theorem tailTrace_708224 : CollatzResearch.WordTrace tailWord_708224 prefixEnd_708224 53875455266658119117473 := by
  unfold tailWord_708224
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915525693116438937293863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17220700924155251916391817 12915525693116438937293863)
  ·
    refine ⟨19373288539674658405940795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12915525693116438937293863 19373288539674658405940795)
    ·
      refine ⟨29059932809511987608911193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19373288539674658405940795 29059932809511987608911193)
      ·
        refine ⟨21794949607133990706683395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29059932809511987608911193 21794949607133990706683395)
        ·
          refine ⟨32692424410700986060025093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21794949607133990706683395 32692424410700986060025093)
          ·
            refine ⟨6129829577006434886254705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32692424410700986060025093 6129829577006434886254705)
            ·
              refine ⟨4597372182754826164691029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6129829577006434886254705 4597372182754826164691029)
              ·
                refine ⟨53875455266658119117473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4597372182754826164691029 53875455266658119117473)
                ·
                  rfl

theorem cell21_708224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_708224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708224 prefixEnd_708224 := by exact prefixLift 708224
  have htrace : WordTrace (prefixWord ++ tailWord_708224) baseStart_708224 baseEnd_708224 := by
    simpa [prefixWord, tailWord_708224, baseEnd_708224] using wordTrace_append hprefix tailTrace_708224
  have hstable : (prefixWord ++ tailWord_708224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708224).length < 2 ^ (prefixWord ++ tailWord_708224).sum := by decide
  have hdescent : baseEnd_708224 < baseStart_708224 := by decide
  rcases family_descends (prefixWord ++ tailWord_708224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708264 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 5]
def baseStart_708264 : Nat := 118140960795 + 708264 * 2 ^ 59
def prefixEnd_708264 : Nat := 4983230072969 + 3 ^ 40 * 708264 * 2
def baseEnd_708264 : Nat := 161635494344943176685671

theorem tailTrace_708264 : CollatzResearch.WordTrace tailWord_708264 prefixEnd_708264 161635494344943176685671 := by
  unfold tailWord_708264
  simp only [CollatzResearch.WordTrace]
  refine ⟨12916255153043982353021923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17221673537391976470695897 12916255153043982353021923)
  ·
    refine ⟨19374382729565973529532885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12916255153043982353021923 19374382729565973529532885)
    ·
      refine ⟨454087095224202504598427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19374382729565973529532885 454087095224202504598427)
      ·
        refine ⟨681130642836303756897641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454087095224202504598427 681130642836303756897641)
        ·
          refine ⟨510847982127227817673231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681130642836303756897641 510847982127227817673231)
          ·
            refine ⟨766271973190841726509847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510847982127227817673231 766271973190841726509847)
            ·
              refine ⟨1149407959786262589764771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766271973190841726509847 1149407959786262589764771)
              ·
                refine ⟨1724111939679393884647157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149407959786262589764771 1724111939679393884647157)
                ·
                  refine ⟨161635494344943176685671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1724111939679393884647157 161635494344943176685671)
                  ·
                    rfl

theorem cell21_708264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_708264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708264 prefixEnd_708264 := by exact prefixLift 708264
  have htrace : WordTrace (prefixWord ++ tailWord_708264) baseStart_708264 baseEnd_708264 := by
    simpa [prefixWord, tailWord_708264, baseEnd_708264] using wordTrace_append hprefix tailTrace_708264
  have hstable : (prefixWord ++ tailWord_708264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708264).length < 2 ^ (prefixWord ++ tailWord_708264).sum := by decide
  have hdescent : baseEnd_708264 < baseStart_708264 := by decide
  rcases family_descends (prefixWord ++ tailWord_708264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708272 : List Nat := [2, 1, 1, 1, 2, 1, 4, 6, 3]
def baseStart_708272 : Nat := 118140960795 + 708272 * 2 ^ 59
def prefixEnd_708272 : Nat := 4983230072969 + 3 ^ 40 * 708272 * 2
def baseEnd_708272 : Nat := 161637320053936940552321

theorem tailTrace_708272 : CollatzResearch.WordTrace tailWord_708272 prefixEnd_708272 161637320053936940552321 := by
  unfold tailWord_708272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12916401045029491036167535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17221868060039321381556713 12916401045029491036167535)
  ·
    refine ⟨19374601567544236554251303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12916401045029491036167535 19374601567544236554251303)
    ·
      refine ⟨29061902351316354831376955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19374601567544236554251303 29061902351316354831376955)
      ·
        refine ⟨43592853526974532247065433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29061902351316354831376955 43592853526974532247065433)
        ·
          refine ⟨32694640145230899185299075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43592853526974532247065433 32694640145230899185299075)
          ·
            refine ⟨49041960217846348777948613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32694640145230899185299075 49041960217846348777948613)
            ·
              refine ⟨9195367540846190395865365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49041960217846348777948613 9195367540846190395865365)
              ·
                refine ⟨431032853477165174806189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9195367540846190395865365 431032853477165174806189)
                ·
                  refine ⟨161637320053936940552321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431032853477165174806189 161637320053936940552321)
                  ·
                    rfl

theorem cell21_708272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_708272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708272 prefixEnd_708272 := by exact prefixLift 708272
  have htrace : WordTrace (prefixWord ++ tailWord_708272) baseStart_708272 baseEnd_708272 := by
    simpa [prefixWord, tailWord_708272, baseEnd_708272] using wordTrace_append hprefix tailTrace_708272
  have hstable : (prefixWord ++ tailWord_708272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708272).length < 2 ^ (prefixWord ++ tailWord_708272).sum := by decide
  have hdescent : baseEnd_708272 < baseStart_708272 := by decide
  rcases family_descends (prefixWord ++ tailWord_708272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708278 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_708278 : Nat := 118140960795 + 708278 * 2 ^ 59
def prefixEnd_708278 : Nat := 4983230072969 + 3 ^ 40 * 708278 * 2
def baseEnd_708278 : Nat := 161638689335682263452309

theorem tailTrace_708278 : CollatzResearch.WordTrace tailWord_708278 prefixEnd_708278 161638689335682263452309 := by
  unfold tailWord_708278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614563808002327818565843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17222013952024830064702325 1614563808002327818565843)
  ·
    refine ⟨2421845712003491727848765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1614563808002327818565843 2421845712003491727848765)
    ·
      refine ⟨908192142001309397943287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2421845712003491727848765 908192142001309397943287)
      ·
        refine ⟨1362288213001964096914931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908192142001309397943287 1362288213001964096914931)
        ·
          refine ⟨2043432319502946145372397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362288213001964096914931 2043432319502946145372397)
          ·
            refine ⟨766287119813604804514649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2043432319502946145372397 766287119813604804514649)
            ·
              refine ⟨574715339860203603385987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766287119813604804514649 574715339860203603385987)
              ·
                refine ⟨862073009790305405078981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574715339860203603385987 862073009790305405078981)
                ·
                  refine ⟨161638689335682263452309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862073009790305405078981 161638689335682263452309)
                  ·
                    rfl

theorem cell21_708278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_708278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708278 prefixEnd_708278 := by exact prefixLift 708278
  have htrace : WordTrace (prefixWord ++ tailWord_708278) baseStart_708278 baseEnd_708278 := by
    simpa [prefixWord, tailWord_708278, baseEnd_708278] using wordTrace_append hprefix tailTrace_708278
  have hstable : (prefixWord ++ tailWord_708278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708278).length < 2 ^ (prefixWord ++ tailWord_708278).sum := by decide
  have hdescent : baseEnd_708278 < baseStart_708278 := by decide
  rcases family_descends (prefixWord ++ tailWord_708278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708317 : List Nat := [1, 4, 3, 3, 10]
def baseStart_708317 : Nat := 118140960795 + 708317 * 2 ^ 59
def prefixEnd_708317 : Nat := 4983230072969 + 3 ^ 40 * 708317 * 2
def baseEnd_708317 : Nat := 1995649255148479781509

theorem tailTrace_708317 : CollatzResearch.WordTrace tailWord_708317 prefixEnd_708317 1995649255148479781509 := by
  unfold tailWord_708317
  simp only [CollatzResearch.WordTrace]
  refine ⟨25834443374895954757723205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17222962249930636505148803 25834443374895954757723205)
  ·
    refine ⟨4843958132792991517073101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25834443374895954757723205 4843958132792991517073101)
    ·
      refine ⟨1816484299797371818902413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4843958132792991517073101 1816484299797371818902413)
      ·
        refine ⟨681181612424014432088405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1816484299797371818902413 681181612424014432088405)
        ·
          refine ⟨1995649255148479781509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 681181612424014432088405 1995649255148479781509)
          ·
            rfl

theorem cell21_708317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 10].length) (baseStart_708317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708317 prefixEnd_708317 := by exact prefixLift 708317
  have htrace : WordTrace (prefixWord ++ tailWord_708317) baseStart_708317 baseEnd_708317 := by
    simpa [prefixWord, tailWord_708317, baseEnd_708317] using wordTrace_append hprefix tailTrace_708317
  have hstable : (prefixWord ++ tailWord_708317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708317).length < 2 ^ (prefixWord ++ tailWord_708317).sum := by decide
  have hdescent : baseEnd_708317 < baseStart_708317 := by decide
  rcases family_descends (prefixWord ++ tailWord_708317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708323 : List Nat := [1, 1, 1, 7, 2, 2, 2, 2, 3]
def baseStart_708323 : Nat := 118140960795 + 708323 * 2 ^ 59
def prefixEnd_708323 : Nat := 4983230072969 + 3 ^ 40 * 708323 * 2
def baseEnd_708323 : Nat := 161648958948772185202217

theorem tailTrace_708323 : CollatzResearch.WordTrace tailWord_708323 prefixEnd_708323 161648958948772185202217 := by
  unfold tailWord_708323
  simp only [CollatzResearch.WordTrace]
  refine ⟨25834662212874217782441623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17223108141916145188294415 25834662212874217782441623)
  ·
    refine ⟨38751993319311326673662435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25834662212874217782441623 38751993319311326673662435)
    ·
      refine ⟨58127989978966990010493653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38751993319311326673662435 58127989978966990010493653)
      ·
        refine ⟨1362374765132038828370945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 58127989978966990010493653 1362374765132038828370945)
        ·
          refine ⟨1021781073849029121278209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1362374765132038828370945 1021781073849029121278209)
          ·
            refine ⟨766335805386771840958657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1021781073849029121278209 766335805386771840958657)
            ·
              refine ⟨574751854040078880718993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766335805386771840958657 574751854040078880718993)
              ·
                refine ⟨431063890530059160539245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574751854040078880718993 431063890530059160539245)
                ·
                  refine ⟨161648958948772185202217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431063890530059160539245 161648958948772185202217)
                  ·
                    rfl

theorem cell21_708323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2, 3].length) (baseStart_708323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708323 prefixEnd_708323 := by exact prefixLift 708323
  have htrace : WordTrace (prefixWord ++ tailWord_708323) baseStart_708323 baseEnd_708323 := by
    simpa [prefixWord, tailWord_708323, baseEnd_708323] using wordTrace_append hprefix tailTrace_708323
  have hstable : (prefixWord ++ tailWord_708323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708323).length < 2 ^ (prefixWord ++ tailWord_708323).sum := by decide
  have hdescent : baseEnd_708323 < baseStart_708323 := by decide
  rcases family_descends (prefixWord ++ tailWord_708323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708345 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 10]
def baseStart_708345 : Nat := 118140960795 + 708345 * 2 ^ 59
def prefixEnd_708345 : Nat := 4983230072969 + 3 ^ 40 * 708345 * 2
def baseEnd_708345 : Nat := 161653979648505035835505

theorem tailTrace_708345 : CollatzResearch.WordTrace tailWord_708345 prefixEnd_708345 161653979648505035835505 := by
  unfold tailWord_708345
  simp only [CollatzResearch.WordTrace]
  refine ⟨25835464618794515539742489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17223643079196343693161659 25835464618794515539742489)
  ·
    refine ⟨19376598464095886654806867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25835464618794515539742489 19376598464095886654806867)
    ·
      refine ⟨29064897696143829982210301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19376598464095886654806867 29064897696143829982210301)
      ·
        refine ⟨10899336636053936243328863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29064897696143829982210301 10899336636053936243328863)
        ·
          refine ⟨16349004954080904364993295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10899336636053936243328863 16349004954080904364993295)
          ·
            refine ⟨24523507431121356547489943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16349004954080904364993295 24523507431121356547489943)
            ·
              refine ⟨36785261146682034821234915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24523507431121356547489943 36785261146682034821234915)
              ·
                refine ⟨55177891720023052231852373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36785261146682034821234915 55177891720023052231852373)
                ·
                  refine ⟨161653979648505035835505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 55177891720023052231852373 161653979648505035835505)
                  ·
                    rfl

theorem cell21_708345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_708345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708345 prefixEnd_708345 := by exact prefixLift 708345
  have htrace : WordTrace (prefixWord ++ tailWord_708345) baseStart_708345 baseEnd_708345 := by
    simpa [prefixWord, tailWord_708345, baseEnd_708345] using wordTrace_append hprefix tailTrace_708345
  have hstable : (prefixWord ++ tailWord_708345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708345).length < 2 ^ (prefixWord ++ tailWord_708345).sum := by decide
  have hdescent : baseEnd_708345 < baseStart_708345 := by decide
  rcases family_descends (prefixWord ++ tailWord_708345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708410 : List Nat := [3, 1, 1, 1, 5, 3, 2, 5]
def baseStart_708410 : Nat := 118140960795 + 708410 * 2 ^ 59
def prefixEnd_708410 : Nat := 4983230072969 + 3 ^ 40 * 708410 * 2
def baseEnd_708410 : Nat := 53889604511359789084013

theorem tailTrace_708410 : CollatzResearch.WordTrace tailWord_708410 prefixEnd_708410 53889604511359789084013 := by
  unfold tailWord_708410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6459458840889757910214671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17225223575706021093905789 6459458840889757910214671)
  ·
    refine ⟨9689188261334636865322007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6459458840889757910214671 9689188261334636865322007)
    ·
      refine ⟨14533782392001955297983011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9689188261334636865322007 14533782392001955297983011)
      ·
        refine ⟨21800673588002932946974517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14533782392001955297983011 21800673588002932946974517)
        ·
          refine ⟨2043813148875274963778861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21800673588002932946974517 2043813148875274963778861)
          ·
            refine ⟨766429930828228111417073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2043813148875274963778861 766429930828228111417073)
            ·
              refine ⟨574822448121171083562805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766429930828228111417073 574822448121171083562805)
              ·
                refine ⟨53889604511359789084013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 574822448121171083562805 53889604511359789084013)
                ·
                  rfl

theorem cell21_708410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_708410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708410 prefixEnd_708410 := by exact prefixLift 708410
  have htrace : WordTrace (prefixWord ++ tailWord_708410) baseStart_708410 baseEnd_708410 := by
    simpa [prefixWord, tailWord_708410, baseEnd_708410] using wordTrace_append hprefix tailTrace_708410
  have hstable : (prefixWord ++ tailWord_708410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708410).length < 2 ^ (prefixWord ++ tailWord_708410).sum := by decide
  have hdescent : baseEnd_708410 < baseStart_708410 := by decide
  rcases family_descends (prefixWord ++ tailWord_708410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708421 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 8]
def baseStart_708421 : Nat := 118140960795 + 708421 * 2 ^ 59
def prefixEnd_708421 : Nat := 4983230072969 + 3 ^ 40 * 708421 * 2
def baseEnd_708421 : Nat := 161671323883945792568683

theorem tailTrace_708421 : CollatzResearch.WordTrace tailWord_708421 prefixEnd_708421 161671323883945792568683 := by
  unfold tailWord_708421
  simp only [CollatzResearch.WordTrace]
  refine ⟨25838236566519180519509117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17225491044346120346339411 25838236566519180519509117)
  ·
    refine ⟨9689338712444692694815919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25838236566519180519509117 9689338712444692694815919)
    ·
      refine ⟨14534008068667039042223879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9689338712444692694815919 14534008068667039042223879)
      ·
        refine ⟨21801012103000558563335819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14534008068667039042223879 21801012103000558563335819)
        ·
          refine ⟨32701518154500837845003729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21801012103000558563335819 32701518154500837845003729)
          ·
            refine ⟨24526138615875628383752797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32701518154500837845003729 24526138615875628383752797)
            ·
              refine ⟨9197301980953360643907299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24526138615875628383752797 9197301980953360643907299)
              ·
                refine ⟨13795952971430040965860949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197301980953360643907299 13795952971430040965860949)
                ·
                  refine ⟨161671323883945792568683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13795952971430040965860949 161671323883945792568683)
                  ·
                    rfl

theorem cell21_708421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_708421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708421 prefixEnd_708421 := by exact prefixLift 708421
  have htrace : WordTrace (prefixWord ++ tailWord_708421) baseStart_708421 baseEnd_708421 := by
    simpa [prefixWord, tailWord_708421, baseEnd_708421] using wordTrace_append hprefix tailTrace_708421
  have hstable : (prefixWord ++ tailWord_708421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708421).length < 2 ^ (prefixWord ++ tailWord_708421).sum := by decide
  have hdescent : baseEnd_708421 < baseStart_708421 := by decide
  rcases family_descends (prefixWord ++ tailWord_708421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708441 : List Nat := [1, 2, 1, 2, 2, 3, 5, 2, 3]
def baseStart_708441 : Nat := 118140960795 + 708441 * 2 ^ 59
def prefixEnd_708441 : Nat := 4983230072969 + 3 ^ 40 * 708441 * 2
def baseEnd_708441 : Nat := 161675888156430202235309

theorem tailTrace_708441 : CollatzResearch.WordTrace tailWord_708441 prefixEnd_708441 161675888156430202235309 := by
  unfold tailWord_708441
  simp only [CollatzResearch.WordTrace]
  refine ⟨25838966026446723935237177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17225977350964482623491451 25838966026446723935237177)
  ·
    refine ⟨19379224519835042951427883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25838966026446723935237177 19379224519835042951427883)
    ·
      refine ⟨29068836779752564427141825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19379224519835042951427883 29068836779752564427141825)
      ·
        refine ⟨21801627584814423320356369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29068836779752564427141825 21801627584814423320356369)
        ·
          refine ⟨16351220688610817490267277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21801627584814423320356369 16351220688610817490267277)
          ·
            refine ⟨6131707758229056558850229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16351220688610817490267277 6131707758229056558850229)
            ·
              refine ⟨574847602333974052392209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6131707758229056558850229 574847602333974052392209)
              ·
                refine ⟨431135701750480539294157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574847602333974052392209 431135701750480539294157)
                ·
                  refine ⟨161675888156430202235309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431135701750480539294157 161675888156430202235309)
                  ·
                    rfl

theorem cell21_708441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_708441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708441 prefixEnd_708441 := by exact prefixLift 708441
  have htrace : WordTrace (prefixWord ++ tailWord_708441) baseStart_708441 baseEnd_708441 := by
    simpa [prefixWord, tailWord_708441, baseEnd_708441] using wordTrace_append hprefix tailTrace_708441
  have hstable : (prefixWord ++ tailWord_708441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708441).length < 2 ^ (prefixWord ++ tailWord_708441).sum := by decide
  have hdescent : baseEnd_708441 < baseStart_708441 := by decide
  rcases family_descends (prefixWord ++ tailWord_708441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708497 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 6]
def baseStart_708497 : Nat := 118140960795 + 708497 * 2 ^ 59
def prefixEnd_708497 : Nat := 4983230072969 + 3 ^ 40 * 708497 * 2
def baseEnd_708497 : Nat := 161688668119386549301861

theorem tailTrace_708497 : CollatzResearch.WordTrace tailWord_708497 prefixEnd_708497 161688668119386549301861 := by
  unfold tailWord_708497
  simp only [CollatzResearch.WordTrace]
  refine ⟨25841008514243845499275745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17227339009495896999517163 25841008514243845499275745)
  ·
    refine ⟨19380756385682884124456809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25841008514243845499275745 19380756385682884124456809)
    ·
      refine ⟨14535567289262163093342607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19380756385682884124456809 14535567289262163093342607)
      ·
        refine ⟨21803350933893244640013911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14535567289262163093342607 21803350933893244640013911)
        ·
          refine ⟨32705026400839866960020867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21803350933893244640013911 32705026400839866960020867)
          ·
            refine ⟨49057539601259800440031301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32705026400839866960020867 49057539601259800440031301)
            ·
              refine ⟨9198288675236212582505869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49057539601259800440031301 9198288675236212582505869)
              ·
                refine ⟨3449358253213579718439701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9198288675236212582505869 3449358253213579718439701)
                ·
                  refine ⟨161688668119386549301861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3449358253213579718439701 161688668119386549301861)
                  ·
                    rfl

theorem cell21_708497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_708497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708497 prefixEnd_708497 := by exact prefixLift 708497
  have htrace : WordTrace (prefixWord ++ tailWord_708497) baseStart_708497 baseEnd_708497 := by
    simpa [prefixWord, tailWord_708497, baseEnd_708497] using wordTrace_append hprefix tailTrace_708497
  have hstable : (prefixWord ++ tailWord_708497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708497).length < 2 ^ (prefixWord ++ tailWord_708497).sum := by decide
  have hdescent : baseEnd_708497 < baseStart_708497 := by decide
  rcases family_descends (prefixWord ++ tailWord_708497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708559 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 5]
def baseStart_708559 : Nat := 118140960795 + 708559 * 2 ^ 59
def prefixEnd_708559 : Nat := 4983230072969 + 3 ^ 40 * 708559 * 2
def baseEnd_708559 : Nat := 161702817364088219268401

theorem tailTrace_708559 : CollatzResearch.WordTrace tailWord_708559 prefixEnd_708559 161702817364088219268401 := by
  unfold tailWord_708559
  simp only [CollatzResearch.WordTrace]
  refine ⟨25843269840019230088032731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17228846560012820058688487 25843269840019230088032731)
  ·
    refine ⟨38764904760028845132049097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25843269840019230088032731 38764904760028845132049097)
    ·
      refine ⟨29073678570021633849036823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38764904760028845132049097 29073678570021633849036823)
      ·
        refine ⟨43610517855032450773555235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29073678570021633849036823 43610517855032450773555235)
        ·
          refine ⟨65415776782548676160332853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43610517855032450773555235 65415776782548676160332853)
          ·
            refine ⟨6132729073363938390031205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65415776782548676160332853 6132729073363938390031205)
            ·
              refine ⟨1149886701255738448130851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6132729073363938390031205 1149886701255738448130851)
              ·
                refine ⟨1724830051883607672196277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149886701255738448130851 1724830051883607672196277)
                ·
                  refine ⟨161702817364088219268401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1724830051883607672196277 161702817364088219268401)
                  ·
                    rfl

theorem cell21_708559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 5].length) (baseStart_708559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708559 prefixEnd_708559 := by exact prefixLift 708559
  have htrace : WordTrace (prefixWord ++ tailWord_708559) baseStart_708559 baseEnd_708559 := by
    simpa [prefixWord, tailWord_708559, baseEnd_708559] using wordTrace_append hprefix tailTrace_708559
  have hstable : (prefixWord ++ tailWord_708559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708559).length < 2 ^ (prefixWord ++ tailWord_708559).sum := by decide
  have hdescent : baseEnd_708559 < baseStart_708559 := by decide
  rcases family_descends (prefixWord ++ tailWord_708559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708590 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_708590 : Nat := 118140960795 + 708590 * 2 ^ 59
def prefixEnd_708590 : Nat := 4983230072969 + 3 ^ 40 * 708590 * 2
def baseEnd_708590 : Nat := 161709891986439054251671

theorem tailTrace_708590 : CollatzResearch.WordTrace tailWord_708590 prefixEnd_708590 161709891986439054251671 := by
  unfold tailWord_708590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3230550062863365297801403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17229600335271281588274149 3230550062863365297801403)
  ·
    refine ⟨4845825094295047946702105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3230550062863365297801403 4845825094295047946702105)
    ·
      refine ⟨3634368820721285960026579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4845825094295047946702105 3634368820721285960026579)
      ·
        refine ⟨5451553231081928940039869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634368820721285960026579 5451553231081928940039869)
        ·
          refine ⟨2044332461655723352514951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5451553231081928940039869 2044332461655723352514951)
          ·
            refine ⟨3066498692483585028772427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044332461655723352514951 3066498692483585028772427)
            ·
              refine ⟨4599748038725377543158641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066498692483585028772427 4599748038725377543158641)
              ·
                refine ⟨3449811029044033157368981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599748038725377543158641 3449811029044033157368981)
                ·
                  refine ⟨161709891986439054251671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3449811029044033157368981 161709891986439054251671)
                  ·
                    rfl

theorem cell21_708590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_708590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708590 prefixEnd_708590 := by exact prefixLift 708590
  have htrace : WordTrace (prefixWord ++ tailWord_708590) baseStart_708590 baseEnd_708590 := by
    simpa [prefixWord, tailWord_708590, baseEnd_708590] using wordTrace_append hprefix tailTrace_708590
  have hstable : (prefixWord ++ tailWord_708590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708590).length < 2 ^ (prefixWord ++ tailWord_708590).sum := by decide
  have hdescent : baseEnd_708590 < baseStart_708590 := by decide
  rcases family_descends (prefixWord ++ tailWord_708590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708762 : List Nat := [3, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_708762 : Nat := 118140960795 + 708762 * 2 ^ 59
def prefixEnd_708762 : Nat := 4983230072969 + 3 ^ 40 * 708762 * 2
def baseEnd_708762 : Nat := 161749144729804977384653

theorem tailTrace_708762 : CollatzResearch.WordTrace tailWord_708762 prefixEnd_708762 161749144729804977384653 := by
  unfold tailWord_708762
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462668464570948939418135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17233782572189197171781693 6462668464570948939418135)
  ·
    refine ⟨9694002696856423409127203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6462668464570948939418135 9694002696856423409127203)
    ·
      refine ⟨14541004045284635113690805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9694002696856423409127203 14541004045284635113690805)
      ·
        refine ⟨1363219129245434541908513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14541004045284635113690805 1363219129245434541908513)
        ·
          refine ⟨1022414346934075906431385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1363219129245434541908513 1022414346934075906431385)
          ·
            refine ⟨766810760200556929823539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022414346934075906431385 766810760200556929823539)
            ·
              refine ⟨1150216140300835394735309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766810760200556929823539 1150216140300835394735309)
              ·
                refine ⟨431331052612813273025741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1150216140300835394735309 431331052612813273025741)
                ·
                  refine ⟨161749144729804977384653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431331052612813273025741 161749144729804977384653)
                  ·
                    rfl

theorem cell21_708762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_708762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708762 prefixEnd_708762 := by exact prefixLift 708762
  have htrace : WordTrace (prefixWord ++ tailWord_708762) baseStart_708762 baseEnd_708762 := by
    simpa [prefixWord, tailWord_708762, baseEnd_708762] using wordTrace_append hprefix tailTrace_708762
  have hstable : (prefixWord ++ tailWord_708762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708762).length < 2 ^ (prefixWord ++ tailWord_708762).sum := by decide
  have hdescent : baseEnd_708762 < baseStart_708762 := by decide
  rcases family_descends (prefixWord ++ tailWord_708762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708815 : List Nat := [1, 1, 2, 1, 1, 3, 3, 9]
def baseStart_708815 : Nat := 118140960795 + 708815 * 2 ^ 59
def prefixEnd_708815 : Nat := 4983230072969 + 3 ^ 40 * 708815 * 2
def baseEnd_708815 : Nat := 53920413350629554333737

theorem tailTrace_708815 : CollatzResearch.WordTrace tailWord_708815 prefixEnd_708815 53920413350629554333737 := by
  unfold tailWord_708815
  simp only [CollatzResearch.WordTrace]
  refine ⟨25852606927091785809351899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17235071284727857206234599 25852606927091785809351899)
  ·
    refine ⟨38778910390637678714027849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25852606927091785809351899 38778910390637678714027849)
    ·
      refine ⟨29084182792978259035520887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38778910390637678714027849 29084182792978259035520887)
      ·
        refine ⟨43626274189467388553281331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29084182792978259035520887 43626274189467388553281331)
        ·
          refine ⟨65439411284201082829921997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43626274189467388553281331 65439411284201082829921997)
          ·
            refine ⟨24539779231575406061220749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65439411284201082829921997 24539779231575406061220749)
            ·
              refine ⟨9202417211840777272957781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24539779231575406061220749 9202417211840777272957781)
              ·
                refine ⟨53920413350629554333737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9202417211840777272957781 53920413350629554333737)
                ·
                  rfl

theorem cell21_708815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 9].length) (baseStart_708815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708815 prefixEnd_708815 := by exact prefixLift 708815
  have htrace : WordTrace (prefixWord ++ tailWord_708815) baseStart_708815 baseEnd_708815 := by
    simpa [prefixWord, tailWord_708815, baseEnd_708815] using wordTrace_append hprefix tailTrace_708815
  have hstable : (prefixWord ++ tailWord_708815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708815).length < 2 ^ (prefixWord ++ tailWord_708815).sum := by decide
  have hdescent : baseEnd_708815 < baseStart_708815 := by decide
  rcases family_descends (prefixWord ++ tailWord_708815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708866 : List Nat := [3, 4, 1, 1, 2, 2, 3, 5]
def baseStart_708866 : Nat := 118140960795 + 708866 * 2 ^ 59
def prefixEnd_708866 : Nat := 4983230072969 + 3 ^ 40 * 708866 * 2
def baseEnd_708866 : Nat := 53924292982241302550369

theorem tailTrace_708866 : CollatzResearch.WordTrace tailWord_708866 prefixEnd_708866 53924292982241302550369 := by
  unfold tailWord_708866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463616762476755379864613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17236311366604681012972301 6463616762476755379864613)
  ·
    refine ⟨1211928142964391633724615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6463616762476755379864613 1211928142964391633724615)
    ·
      refine ⟨1817892214446587450586923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211928142964391633724615 1817892214446587450586923)
      ·
        refine ⟨2726838321669881175880385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817892214446587450586923 2726838321669881175880385)
        ·
          refine ⟨2045128741252410881910289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2726838321669881175880385 2045128741252410881910289)
          ·
            refine ⟨1533846555939308161432717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045128741252410881910289 1533846555939308161432717)
            ·
              refine ⟨575192458477240560537269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1533846555939308161432717 575192458477240560537269)
              ·
                refine ⟨53924292982241302550369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 575192458477240560537269 53924292982241302550369)
                ·
                  rfl

theorem cell21_708866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_708866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708866 prefixEnd_708866 := by exact prefixLift 708866
  have htrace : WordTrace (prefixWord ++ tailWord_708866) baseStart_708866 baseEnd_708866 := by
    simpa [prefixWord, tailWord_708866, baseEnd_708866] using wordTrace_append hprefix tailTrace_708866
  have hstable : (prefixWord ++ tailWord_708866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708866).length < 2 ^ (prefixWord ++ tailWord_708866).sum := by decide
  have hdescent : baseEnd_708866 < baseStart_708866 := by decide
  rcases family_descends (prefixWord ++ tailWord_708866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708939 : List Nat := [1, 1, 1, 1, 3, 1, 1, 9, 3]
def baseStart_708939 : Nat := 118140960795 + 708939 * 2 ^ 59
def prefixEnd_708939 : Nat := 4983230072969 + 3 ^ 40 * 708939 * 2
def baseEnd_708939 : Nat := 161789538541292002934291

theorem tailTrace_708939 : CollatzResearch.WordTrace tailWord_708939 prefixEnd_708939 161789538541292002934291 := by
  unfold tailWord_708939
  simp only [CollatzResearch.WordTrace]
  refine ⟨25857129578642554986865871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17238086385761703324577247 25857129578642554986865871)
  ·
    refine ⟨38785694367963832480298807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25857129578642554986865871 38785694367963832480298807)
    ·
      refine ⟨58178541551945748720448211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38785694367963832480298807 58178541551945748720448211)
      ·
        refine ⟨87267812327918623080672317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58178541551945748720448211 87267812327918623080672317)
        ·
          refine ⟨32725429622969483655252119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87267812327918623080672317 32725429622969483655252119)
          ·
            refine ⟨49088144434454225482878179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32725429622969483655252119 49088144434454225482878179)
            ·
              refine ⟨73632216651681338224317269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49088144434454225482878179 73632216651681338224317269)
              ·
                refine ⟨431438769443445341158109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 73632216651681338224317269 431438769443445341158109)
                ·
                  refine ⟨161789538541292002934291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431438769443445341158109 161789538541292002934291)
                  ·
                    rfl

theorem cell21_708939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 3].length) (baseStart_708939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708939 prefixEnd_708939 := by exact prefixLift 708939
  have htrace : WordTrace (prefixWord ++ tailWord_708939) baseStart_708939 baseEnd_708939 := by
    simpa [prefixWord, tailWord_708939, baseEnd_708939] using wordTrace_append hprefix tailTrace_708939
  have hstable : (prefixWord ++ tailWord_708939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708939).length < 2 ^ (prefixWord ++ tailWord_708939).sum := by decide
  have hdescent : baseEnd_708939 < baseStart_708939 := by decide
  rcases family_descends (prefixWord ++ tailWord_708939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708953 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 4]
def baseStart_708953 : Nat := 118140960795 + 708953 * 2 ^ 59
def prefixEnd_708953 : Nat := 4983230072969 + 3 ^ 40 * 708953 * 2
def baseEnd_708953 : Nat := 161792733532031089700929

theorem tailTrace_708953 : CollatzResearch.WordTrace tailWord_708953 prefixEnd_708953 161792733532031089700929 := by
  unfold tailWord_708953
  simp only [CollatzResearch.WordTrace]
  refine ⟨25857640200591835377875513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17238426800394556918583675 25857640200591835377875513)
  ·
    refine ⟨19393230150443876533406635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25857640200591835377875513 19393230150443876533406635)
    ·
      refine ⟨29089845225665814800109953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19393230150443876533406635 29089845225665814800109953)
      ·
        refine ⟨21817383919249361100082465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29089845225665814800109953 21817383919249361100082465)
        ·
          refine ⟨16363037939437020825061849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21817383919249361100082465 16363037939437020825061849)
          ·
            refine ⟨12272278454577765618796387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16363037939437020825061849 12272278454577765618796387)
            ·
              refine ⟨18408417681866648428194581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12272278454577765618796387 18408417681866648428194581)
              ·
                refine ⟨862894578837499145071621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18408417681866648428194581 862894578837499145071621)
                ·
                  refine ⟨161792733532031089700929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862894578837499145071621 161792733532031089700929)
                  ·
                    rfl

theorem cell21_708953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_708953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_708953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_708953 prefixEnd_708953 := by exact prefixLift 708953
  have htrace : WordTrace (prefixWord ++ tailWord_708953) baseStart_708953 baseEnd_708953 := by
    simpa [prefixWord, tailWord_708953, baseEnd_708953] using wordTrace_append hprefix tailTrace_708953
  have hstable : (prefixWord ++ tailWord_708953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708953).length < 2 ^ (prefixWord ++ tailWord_708953).sum := by decide
  have hdescent : baseEnd_708953 < baseStart_708953 := by decide
  rcases family_descends (prefixWord ++ tailWord_708953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709029 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 4]
def baseStart_709029 : Nat := 118140960795 + 709029 * 2 ^ 59
def prefixEnd_709029 : Nat := 4983230072969 + 3 ^ 40 * 709029 * 2
def baseEnd_709029 : Nat := 161810077767471846434107

theorem tailTrace_709029 : CollatzResearch.WordTrace tailWord_709029 prefixEnd_709029 161810077767471846434107 := by
  unfold tailWord_709029
  simp only [CollatzResearch.WordTrace]
  refine ⟨25860412148316500357642141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17240274765544333571761427 25860412148316500357642141)
  ·
    refine ⟨9697654555618687634115803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25860412148316500357642141 9697654555618687634115803)
    ·
      refine ⟨14546481833428031451173705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9697654555618687634115803 14546481833428031451173705)
      ·
        refine ⟨10909861375071023588380279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14546481833428031451173705 10909861375071023588380279)
        ·
          refine ⟨16364792062606535382570419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10909861375071023588380279 16364792062606535382570419)
          ·
            refine ⟨24547188093909803073855629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16364792062606535382570419 24547188093909803073855629)
            ·
              refine ⟨9205195535216176152695861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24547188093909803073855629 9205195535216176152695861)
              ·
                refine ⟨862987081426516514315237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9205195535216176152695861 862987081426516514315237)
                ·
                  refine ⟨161810077767471846434107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862987081426516514315237 161810077767471846434107)
                  ·
                    rfl

theorem cell21_709029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_709029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709029 prefixEnd_709029 := by exact prefixLift 709029
  have htrace : WordTrace (prefixWord ++ tailWord_709029) baseStart_709029 baseEnd_709029 := by
    simpa [prefixWord, tailWord_709029, baseEnd_709029] using wordTrace_append hprefix tailTrace_709029
  have hstable : (prefixWord ++ tailWord_709029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709029).length < 2 ^ (prefixWord ++ tailWord_709029).sum := by decide
  have hdescent : baseEnd_709029 < baseStart_709029 := by decide
  rcases family_descends (prefixWord ++ tailWord_709029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709032 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_709032 : Nat := 118140960795 + 709032 * 2 ^ 59
def prefixEnd_709032 : Nat := 4983230072969 + 3 ^ 40 * 709032 * 2
def baseEnd_709032 : Nat := 161810762408344507884101

theorem tailTrace_709032 : CollatzResearch.WordTrace tailWord_709032 prefixEnd_709032 161810762408344507884101 := by
  unfold tailWord_709032
  simp only [CollatzResearch.WordTrace]
  refine ⟨12930260783652815935000675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17240347711537087913334233 12930260783652815935000675)
  ·
    refine ⟨19395391175479223902501013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12930260783652815935000675 19395391175479223902501013)
    ·
      refine ⟨909158961350588620429735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19395391175479223902501013 909158961350588620429735)
      ·
        refine ⟨1363738442025882930644603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909158961350588620429735 1363738442025882930644603)
        ·
          refine ⟨2045607663038824395966905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363738442025882930644603 2045607663038824395966905)
          ·
            refine ⟨1534205747279118296975179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045607663038824395966905 1534205747279118296975179)
            ·
              refine ⟨2301308620918677445462769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1534205747279118296975179 2301308620918677445462769)
              ·
                refine ⟨1725981465689008084097077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301308620918677445462769 1725981465689008084097077)
                ·
                  refine ⟨161810762408344507884101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1725981465689008084097077 161810762408344507884101)
                  ·
                    rfl

theorem cell21_709032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_709032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709032 prefixEnd_709032 := by exact prefixLift 709032
  have htrace : WordTrace (prefixWord ++ tailWord_709032) baseStart_709032 baseEnd_709032 := by
    simpa [prefixWord, tailWord_709032, baseEnd_709032] using wordTrace_append hprefix tailTrace_709032
  have hstable : (prefixWord ++ tailWord_709032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709032).length < 2 ^ (prefixWord ++ tailWord_709032).sum := by decide
  have hdescent : baseEnd_709032 < baseStart_709032 := by decide
  rcases family_descends (prefixWord ++ tailWord_709032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709164 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_709164 : Nat := 118140960795 + 709164 * 2 ^ 59
def prefixEnd_709164 : Nat := 4983230072969 + 3 ^ 40 * 709164 * 2
def baseEnd_709164 : Nat := 161840886606741611683831

theorem tailTrace_709164 : CollatzResearch.WordTrace tailWord_709164 prefixEnd_709164 161840886606741611683831 := by
  unfold tailWord_709164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12932668001413709206903273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17243557335218278942537697 12932668001413709206903273)
  ·
    refine ⟨9699501001060281905177455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12932668001413709206903273 9699501001060281905177455)
    ·
      refine ⟨14549251501590422857766183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9699501001060281905177455 14549251501590422857766183)
      ·
        refine ⟨21823877252385634286649275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14549251501590422857766183 21823877252385634286649275)
        ·
          refine ⟨32735815878578451429973913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21823877252385634286649275 32735815878578451429973913)
          ·
            refine ⟨24551861908933838572480435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32735815878578451429973913 24551861908933838572480435)
            ·
              refine ⟨36827792863400757858720653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24551861908933838572480435 36827792863400757858720653)
              ·
                refine ⟨13810422323775284197020245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36827792863400757858720653 13810422323775284197020245)
                ·
                  refine ⟨161840886606741611683831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13810422323775284197020245 161840886606741611683831)
                  ·
                    rfl

theorem cell21_709164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_709164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709164 prefixEnd_709164 := by exact prefixLift 709164
  have htrace : WordTrace (prefixWord ++ tailWord_709164) baseStart_709164 baseEnd_709164 := by
    simpa [prefixWord, tailWord_709164, baseEnd_709164] using wordTrace_append hprefix tailTrace_709164
  have hstable : (prefixWord ++ tailWord_709164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709164).length < 2 ^ (prefixWord ++ tailWord_709164).sum := by decide
  have hdescent : baseEnd_709164 < baseStart_709164 := by decide
  rcases family_descends (prefixWord ++ tailWord_709164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709184 : List Nat := [2, 1, 1, 2, 2, 2, 6, 2, 3]
def baseStart_709184 : Nat := 118140960795 + 709184 * 2 ^ 59
def prefixEnd_709184 : Nat := 4983230072969 + 3 ^ 40 * 709184 * 2
def baseEnd_709184 : Nat := 161845450879226021350457

theorem tailTrace_709184 : CollatzResearch.WordTrace tailWord_709184 prefixEnd_709184 161845450879226021350457 := by
  unfold tailWord_709184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12933032731377480914767303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17244043641836641219689737 12933032731377480914767303)
  ·
    refine ⟨19399549097066221372150955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12933032731377480914767303 19399549097066221372150955)
    ·
      refine ⟨29099323645599332058226433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19399549097066221372150955 29099323645599332058226433)
      ·
        refine ⟨21824492734199499043669825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29099323645599332058226433 21824492734199499043669825)
        ·
          refine ⟨16368369550649624282752369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21824492734199499043669825 16368369550649624282752369)
          ·
            refine ⟨12276277162987218212064277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16368369550649624282752369 12276277162987218212064277)
            ·
              refine ⟨575450492015025853690513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12276277162987218212064277 575450492015025853690513)
              ·
                refine ⟨431587869011269390267885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575450492015025853690513 431587869011269390267885)
                ·
                  refine ⟨161845450879226021350457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431587869011269390267885 161845450879226021350457)
                  ·
                    rfl

theorem cell21_709184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_709184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709184 prefixEnd_709184 := by exact prefixLift 709184
  have htrace : WordTrace (prefixWord ++ tailWord_709184) baseStart_709184 baseEnd_709184 := by
    simpa [prefixWord, tailWord_709184, baseEnd_709184] using wordTrace_append hprefix tailTrace_709184
  have hstable : (prefixWord ++ tailWord_709184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709184).length < 2 ^ (prefixWord ++ tailWord_709184).sum := by decide
  have hdescent : baseEnd_709184 < baseStart_709184 := by decide
  rcases family_descends (prefixWord ++ tailWord_709184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709195 : List Nat := [1, 1, 1, 1, 3, 1, 7, 6]
def baseStart_709195 : Nat := 118140960795 + 709195 * 2 ^ 59
def prefixEnd_709195 : Nat := 4983230072969 + 3 ^ 40 * 709195 * 2
def baseEnd_709195 : Nat := 53949320409697482222367

theorem tailTrace_709195 : CollatzResearch.WordTrace tailWord_709195 prefixEnd_709195 53949320409697482222367 := by
  unfold tailWord_709195
  simp only [CollatzResearch.WordTrace]
  refine ⟨25866466665715110708185039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17244311110476740472123359 25866466665715110708185039)
  ·
    refine ⟨38799699998572666062277559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25866466665715110708185039 38799699998572666062277559)
    ·
      refine ⟨58199549997858999093416339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38799699998572666062277559 58199549997858999093416339)
      ·
        refine ⟨87299324996788498640124509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58199549997858999093416339 87299324996788498640124509)
        ·
          refine ⟨32737246873795686990046691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87299324996788498640124509 32737246873795686990046691)
          ·
            refine ⟨49105870310693530485070037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32737246873795686990046691 49105870310693530485070037)
            ·
              refine ⟨1150918835406879620743829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49105870310693530485070037 1150918835406879620743829)
              ·
                refine ⟨53949320409697482222367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1150918835406879620743829 53949320409697482222367)
                ·
                  rfl

theorem cell21_709195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 6].length) (baseStart_709195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709195 prefixEnd_709195 := by exact prefixLift 709195
  have htrace : WordTrace (prefixWord ++ tailWord_709195) baseStart_709195 baseEnd_709195 := by
    simpa [prefixWord, tailWord_709195, baseEnd_709195] using wordTrace_append hprefix tailTrace_709195
  have hstable : (prefixWord ++ tailWord_709195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709195).length < 2 ^ (prefixWord ++ tailWord_709195).sum := by decide
  have hdescent : baseEnd_709195 < baseStart_709195 := by decide
  rcases family_descends (prefixWord ++ tailWord_709195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709218 : List Nat := [3, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_709218 : Nat := 118140960795 + 709218 * 2 ^ 59
def prefixEnd_709218 : Nat := 4983230072969 + 3 ^ 40 * 709218 * 2
def baseEnd_709218 : Nat := 161853210142449517783721

theorem tailTrace_709218 : CollatzResearch.WordTrace tailWord_709218 prefixEnd_709218 161853210142449517783721 := by
  unfold tailWord_709218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6466826386157946409068077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17244870363087857090848205 6466826386157946409068077)
  ·
    refine ⟨2425059894809229903400529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6466826386157946409068077 2425059894809229903400529)
    ·
      refine ⟨1818794921106922427550397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2425059894809229903400529 1818794921106922427550397)
      ·
        refine ⟨682048095415095910331399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1818794921106922427550397 682048095415095910331399)
        ·
          refine ⟨1023072143122643865497099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682048095415095910331399 1023072143122643865497099)
          ·
            refine ⟨1534608214683965798245649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023072143122643865497099 1534608214683965798245649)
            ·
              refine ⟨1150956161012974348684237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534608214683965798245649 1150956161012974348684237)
              ·
                refine ⟨431608560379865380756589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1150956161012974348684237 431608560379865380756589)
                ·
                  refine ⟨161853210142449517783721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431608560379865380756589 161853210142449517783721)
                  ·
                    rfl

theorem cell21_709218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_709218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709218 prefixEnd_709218 := by exact prefixLift 709218
  have htrace : WordTrace (prefixWord ++ tailWord_709218) baseStart_709218 baseEnd_709218 := by
    simpa [prefixWord, tailWord_709218, baseEnd_709218] using wordTrace_append hprefix tailTrace_709218
  have hstable : (prefixWord ++ tailWord_709218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709218).length < 2 ^ (prefixWord ++ tailWord_709218).sum := by decide
  have hdescent : baseEnd_709218 < baseStart_709218 := by decide
  rcases family_descends (prefixWord ++ tailWord_709218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709226 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_709226 : Nat := 118140960795 + 709226 * 2 ^ 59
def prefixEnd_709226 : Nat := 4983230072969 + 3 ^ 40 * 709226 * 2
def baseEnd_709226 : Nat := 161855035851443281650371

theorem tailTrace_709226 : CollatzResearch.WordTrace tailWord_709226 prefixEnd_709226 161855035851443281650371 := by
  unfold tailWord_709226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6466899332150700750640883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17245064885735202001709021 6466899332150700750640883)
  ·
    refine ⟨9700348998226051125961325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6466899332150700750640883 9700348998226051125961325)
    ·
      refine ⟨3637630874334769172235497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9700348998226051125961325 3637630874334769172235497)
      ·
        refine ⟨2728223155751076879176623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3637630874334769172235497 2728223155751076879176623)
        ·
          refine ⟨4092334733626615318764935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2728223155751076879176623 4092334733626615318764935)
          ·
            refine ⟨6138502100439922978147403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092334733626615318764935 6138502100439922978147403)
            ·
              refine ⟨9207753150659884467221105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138502100439922978147403 9207753150659884467221105)
              ·
                refine ⟨6905814862994913350415829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9207753150659884467221105 6905814862994913350415829)
                ·
                  refine ⟨161855035851443281650371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6905814862994913350415829 161855035851443281650371)
                  ·
                    rfl

theorem cell21_709226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_709226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709226 prefixEnd_709226 := by exact prefixLift 709226
  have htrace : WordTrace (prefixWord ++ tailWord_709226) baseStart_709226 baseEnd_709226 := by
    simpa [prefixWord, tailWord_709226, baseEnd_709226] using wordTrace_append hprefix tailTrace_709226
  have hstable : (prefixWord ++ tailWord_709226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709226).length < 2 ^ (prefixWord ++ tailWord_709226).sum := by decide
  have hdescent : baseEnd_709226 < baseStart_709226 := by decide
  rcases family_descends (prefixWord ++ tailWord_709226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709240 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_709240 : Nat := 118140960795 + 709240 * 2 ^ 59
def prefixEnd_709240 : Nat := 4983230072969 + 3 ^ 40 * 709240 * 2
def baseEnd_709240 : Nat := 161858230842182368417009

theorem tailTrace_709240 : CollatzResearch.WordTrace tailWord_709240 prefixEnd_709240 161858230842182368417009 := by
  unfold tailWord_709240
  simp only [CollatzResearch.WordTrace]
  refine ⟨12934053975276041696786587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17245405300368055595715449 12934053975276041696786587)
  ·
    refine ⟨19401080962914062545179881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12934053975276041696786587 19401080962914062545179881)
    ·
      refine ⟨14550810722185546908884911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19401080962914062545179881 14550810722185546908884911)
      ·
        refine ⟨21826216083278320363327367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14550810722185546908884911 21826216083278320363327367)
        ·
          refine ⟨32739324124917480544991051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21826216083278320363327367 32739324124917480544991051)
          ·
            refine ⟨49108986187376220817486577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32739324124917480544991051 49108986187376220817486577)
            ·
              refine ⟨36831739640532165613114933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49108986187376220817486577 36831739640532165613114933)
              ·
                refine ⟨3452975591299890526229525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36831739640532165613114933 3452975591299890526229525)
                ·
                  refine ⟨161858230842182368417009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3452975591299890526229525 161858230842182368417009)
                  ·
                    rfl

theorem cell21_709240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_709240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709240 prefixEnd_709240 := by exact prefixLift 709240
  have htrace : WordTrace (prefixWord ++ tailWord_709240) baseStart_709240 baseEnd_709240 := by
    simpa [prefixWord, tailWord_709240, baseEnd_709240] using wordTrace_append hprefix tailTrace_709240
  have hstable : (prefixWord ++ tailWord_709240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709240).length < 2 ^ (prefixWord ++ tailWord_709240).sum := by decide
  have hdescent : baseEnd_709240 < baseStart_709240 := by decide
  rcases family_descends (prefixWord ++ tailWord_709240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709271 : List Nat := [1, 1, 3, 3, 2, 1, 3, 7]
def baseStart_709271 : Nat := 118140960795 + 709271 * 2 ^ 59
def prefixEnd_709271 : Nat := 4983230072969 + 3 ^ 40 * 709271 * 2
def baseEnd_709271 : Nat := 53955101821511067800093

theorem tailTrace_709271 : CollatzResearch.WordTrace tailWord_709271 prefixEnd_709271 53955101821511067800093 := by
  unfold tailWord_709271
  simp only [CollatzResearch.WordTrace]
  refine ⟨25869238613439775687951667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17246159075626517125301111 25869238613439775687951667)
  ·
    refine ⟨38803857920159663531927501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25869238613439775687951667 38803857920159663531927501)
    ·
      refine ⟨14551446720059873824472813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38803857920159663531927501 14551446720059873824472813)
      ·
        refine ⟨5456792520022452684177305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14551446720059873824472813 5456792520022452684177305)
        ·
          refine ⟨4092594390016839513132979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5456792520022452684177305 4092594390016839513132979)
          ·
            refine ⟨6138891585025259269699469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092594390016839513132979 6138891585025259269699469)
            ·
              refine ⟨2302084344384472226137301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6138891585025259269699469 2302084344384472226137301)
              ·
                refine ⟨53955101821511067800093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2302084344384472226137301 53955101821511067800093)
                ·
                  rfl

theorem cell21_709271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 7].length) (baseStart_709271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709271 prefixEnd_709271 := by exact prefixLift 709271
  have htrace : WordTrace (prefixWord ++ tailWord_709271) baseStart_709271 baseEnd_709271 := by
    simpa [prefixWord, tailWord_709271, baseEnd_709271] using wordTrace_append hprefix tailTrace_709271
  have hstable : (prefixWord ++ tailWord_709271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709271).length < 2 ^ (prefixWord ++ tailWord_709271).sum := by decide
  have hdescent : baseEnd_709271 < baseStart_709271 := by decide
  rcases family_descends (prefixWord ++ tailWord_709271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709294 : List Nat := [4, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_709294 : Nat := 118140960795 + 709294 * 2 ^ 59
def prefixEnd_709294 : Nat := 4983230072969 + 3 ^ 40 * 709294 * 2
def baseEnd_709294 : Nat := 161870554377890274516899

theorem tailTrace_709294 : CollatzResearch.WordTrace tailWord_709294 prefixEnd_709294 161870554377890274516899 := by
  unfold tailWord_709294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233759686544556327004867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17246718328237633744025957 3233759686544556327004867)
  ·
    refine ⟨4850639529816834490507301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3233759686544556327004867 4850639529816834490507301)
    ·
      refine ⟨909494911840656466970119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4850639529816834490507301 909494911840656466970119)
      ·
        refine ⟨1364242367760984700455179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909494911840656466970119 1364242367760984700455179)
        ·
          refine ⟨2046363551641477050682769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364242367760984700455179 2046363551641477050682769)
          ·
            refine ⟨1534772663731107788012077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2046363551641477050682769 1534772663731107788012077)
            ·
              refine ⟨575539748899165420504529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1534772663731107788012077 575539748899165420504529)
              ·
                refine ⟨431654811674374065378397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575539748899165420504529 431654811674374065378397)
                ·
                  refine ⟨161870554377890274516899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431654811674374065378397 161870554377890274516899)
                  ·
                    rfl

theorem cell21_709294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_709294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709294 prefixEnd_709294 := by exact prefixLift 709294
  have htrace : WordTrace (prefixWord ++ tailWord_709294) baseStart_709294 baseEnd_709294 := by
    simpa [prefixWord, tailWord_709294, baseEnd_709294] using wordTrace_append hprefix tailTrace_709294
  have hstable : (prefixWord ++ tailWord_709294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709294).length < 2 ^ (prefixWord ++ tailWord_709294).sum := by decide
  have hdescent : baseEnd_709294 < baseStart_709294 := by decide
  rcases family_descends (prefixWord ++ tailWord_709294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709347 : List Nat := [1, 1, 1, 7, 1, 10]
def baseStart_709347 : Nat := 118140960795 + 709347 * 2 ^ 59
def prefixEnd_709347 : Nat := 4983230072969 + 3 ^ 40 * 709347 * 2
def baseEnd_709347 : Nat := 5995653692591628153091

theorem tailTrace_709347 : CollatzResearch.WordTrace tailWord_709347 prefixEnd_709347 5995653692591628153091 := by
  unfold tailWord_709347
  simp only [CollatzResearch.WordTrace]
  refine ⟨25872010561164440667718295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17248007040776293778478863 25872010561164440667718295)
  ·
    refine ⟨38808015841746661001577443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25872010561164440667718295 38808015841746661001577443)
    ·
      refine ⟨58212023762619991502366165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38808015841746661001577443 58212023762619991502366165)
      ·
        refine ⟨1364344306936406050836707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 58212023762619991502366165 1364344306936406050836707)
        ·
          refine ⟨2046516460404609076255061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364344306936406050836707 2046516460404609076255061)
          ·
            refine ⟨5995653692591628153091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2046516460404609076255061 5995653692591628153091)
            ·
              rfl

theorem cell21_709347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 10].length) (baseStart_709347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709347 prefixEnd_709347 := by exact prefixLift 709347
  have htrace : WordTrace (prefixWord ++ tailWord_709347) baseStart_709347 baseEnd_709347 := by
    simpa [prefixWord, tailWord_709347, baseEnd_709347] using wordTrace_append hprefix tailTrace_709347
  have hstable : (prefixWord ++ tailWord_709347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709347).length < 2 ^ (prefixWord ++ tailWord_709347).sum := by decide
  have hdescent : baseEnd_709347 < baseStart_709347 := by decide
  rcases family_descends (prefixWord ++ tailWord_709347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709395 : List Nat := [1, 1, 1, 2, 1, 3, 6, 3, 3]
def baseStart_709395 : Nat := 118140960795 + 709395 * 2 ^ 59
def prefixEnd_709395 : Nat := 4983230072969 + 3 ^ 40 * 709395 * 2
def baseEnd_709395 : Nat := 161893603953936543333359

theorem tailTrace_709395 : CollatzResearch.WordTrace tailWord_709395 prefixEnd_709395 161893603953936543333359 := by
  unfold tailWord_709395
  simp only [CollatzResearch.WordTrace]
  refine ⟨25873761264990544865465639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17249174176660363243643759 25873761264990544865465639)
  ·
    refine ⟨38810641897485817298198459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25873761264990544865465639 38810641897485817298198459)
    ·
      refine ⟨58215962846228725947297689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38810641897485817298198459 58215962846228725947297689)
      ·
        refine ⟨43661972134671544460473267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58215962846228725947297689 43661972134671544460473267)
        ·
          refine ⟨65492958202007316690709901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43661972134671544460473267 65492958202007316690709901)
          ·
            refine ⟨24559859325752743759016213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65492958202007316690709901 24559859325752743759016213)
            ·
              refine ⟨1151243405894659863703885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24559859325752743759016213 1151243405894659863703885)
              ·
                refine ⟨431716277210497448888957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151243405894659863703885 431716277210497448888957)
                ·
                  refine ⟨161893603953936543333359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431716277210497448888957 161893603953936543333359)
                  ·
                    rfl

theorem cell21_709395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 3].length) (baseStart_709395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709395 prefixEnd_709395 := by exact prefixLift 709395
  have htrace : WordTrace (prefixWord ++ tailWord_709395) baseStart_709395 baseEnd_709395 := by
    simpa [prefixWord, tailWord_709395, baseEnd_709395] using wordTrace_append hprefix tailTrace_709395
  have hstable : (prefixWord ++ tailWord_709395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709395).length < 2 ^ (prefixWord ++ tailWord_709395).sum := by decide
  have hdescent : baseEnd_709395 < baseStart_709395 := by decide
  rcases family_descends (prefixWord ++ tailWord_709395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709426 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_709426 : Nat := 118140960795 + 709426 * 2 ^ 59
def prefixEnd_709426 : Nat := 4983230072969 + 3 ^ 40 * 709426 * 2
def baseEnd_709426 : Nat := 161900678576287378316629

theorem tailTrace_709426 : CollatzResearch.WordTrace tailWord_709426 prefixEnd_709426 161900678576287378316629 := by
  unfold tailWord_709426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6468722981969559289961033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17249927951918824773229421 6468722981969559289961033)
  ·
    refine ⟨4851542236477169467470775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6468722981969559289961033 4851542236477169467470775)
    ·
      refine ⟨7277313354715754201206163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4851542236477169467470775 7277313354715754201206163)
      ·
        refine ⟨10915970032073631301809245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7277313354715754201206163 10915970032073631301809245)
        ·
          refine ⟨4093488762027611738178467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10915970032073631301809245 4093488762027611738178467)
          ·
            refine ⟨6140233143041417607267701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093488762027611738178467 6140233143041417607267701)
            ·
              refine ⟨575646857160132900681347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6140233143041417607267701 575646857160132900681347)
              ·
                refine ⟨863470285740199351022021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575646857160132900681347 863470285740199351022021)
                ·
                  refine ⟨161900678576287378316629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 863470285740199351022021 161900678576287378316629)
                  ·
                    rfl

theorem cell21_709426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_709426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709426 prefixEnd_709426 := by exact prefixLift 709426
  have htrace : WordTrace (prefixWord ++ tailWord_709426) baseStart_709426 baseEnd_709426 := by
    simpa [prefixWord, tailWord_709426, baseEnd_709426] using wordTrace_append hprefix tailTrace_709426
  have hstable : (prefixWord ++ tailWord_709426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709426).length < 2 ^ (prefixWord ++ tailWord_709426).sum := by decide
  have hdescent : baseEnd_709426 < baseStart_709426 := by decide
  rcases family_descends (prefixWord ++ tailWord_709426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709522 : List Nat := [3, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_709522 : Nat := 118140960795 + 709522 * 2 ^ 59
def prefixEnd_709522 : Nat := 4983230072969 + 3 ^ 40 * 709522 * 2
def baseEnd_709522 : Nat := 161922587084212544716433

theorem tailTrace_709522 : CollatzResearch.WordTrace tailWord_709522 prefixEnd_709522 161922587084212544716433 := by
  unfold tailWord_709522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469598333882611388834705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17252262223686963703559213 6469598333882611388834705)
  ·
    refine ⟨4852198750411958541626029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6469598333882611388834705 4852198750411958541626029)
    ·
      refine ⟨1819574531404484453109761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4852198750411958541626029 1819574531404484453109761)
      ·
        refine ⟨1364680898553363339832321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1819574531404484453109761 1364680898553363339832321)
        ·
          refine ⟨1023510673915022504874241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1364680898553363339832321 1023510673915022504874241)
          ·
            refine ⟨767633005436266878655681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023510673915022504874241 767633005436266878655681)
            ·
              refine ⟨575724754077200158991761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767633005436266878655681 575724754077200158991761)
              ·
                refine ⟨431793565557900119243821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575724754077200158991761 431793565557900119243821)
                ·
                  refine ⟨161922587084212544716433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431793565557900119243821 161922587084212544716433)
                  ·
                    rfl

theorem cell21_709522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_709522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709522 prefixEnd_709522 := by exact prefixLift 709522
  have htrace : WordTrace (prefixWord ++ tailWord_709522) baseStart_709522 baseEnd_709522 := by
    simpa [prefixWord, tailWord_709522, baseEnd_709522] using wordTrace_append hprefix tailTrace_709522
  have hstable : (prefixWord ++ tailWord_709522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709522).length < 2 ^ (prefixWord ++ tailWord_709522).sum := by decide
  have hdescent : baseEnd_709522 < baseStart_709522 := by decide
  rcases family_descends (prefixWord ++ tailWord_709522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709640 : List Nat := [2, 1, 3, 2, 1, 4, 3, 2, 3]
def baseStart_709640 : Nat := 118140960795 + 709640 * 2 ^ 59
def prefixEnd_709640 : Nat := 4983230072969 + 3 ^ 40 * 709640 * 2
def baseEnd_709640 : Nat := 161949516291870561749525

theorem tailTrace_709640 : CollatzResearch.WordTrace tailWord_709640 prefixEnd_709640 161949516291870561749525 := by
  unfold tailWord_709640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12941348574551475854067187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17255131432735301138756249 12941348574551475854067187)
  ·
    refine ⟨19412022861827213781100781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12941348574551475854067187 19412022861827213781100781)
    ·
      refine ⟨7279508573185205167912793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19412022861827213781100781 7279508573185205167912793)
      ·
        refine ⟨5459631429888903875934595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7279508573185205167912793 5459631429888903875934595)
        ·
          refine ⟨8189447144833355813901893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5459631429888903875934595 8189447144833355813901893)
          ·
            refine ⟨1535521339656254215106605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8189447144833355813901893 1535521339656254215106605)
            ·
              refine ⟨575820502371095330664977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1535521339656254215106605 575820502371095330664977)
              ·
                refine ⟨431865376778321497998733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575820502371095330664977 431865376778321497998733)
                ·
                  refine ⟨161949516291870561749525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431865376778321497998733 161949516291870561749525)
                  ·
                    rfl

theorem cell21_709640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_709640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709640 prefixEnd_709640 := by exact prefixLift 709640
  have htrace : WordTrace (prefixWord ++ tailWord_709640) baseStart_709640 baseEnd_709640 := by
    simpa [prefixWord, tailWord_709640, baseEnd_709640] using wordTrace_append hprefix tailTrace_709640
  have hstable : (prefixWord ++ tailWord_709640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709640).length < 2 ^ (prefixWord ++ tailWord_709640).sum := by decide
  have hdescent : baseEnd_709640 < baseStart_709640 := by decide
  rcases family_descends (prefixWord ++ tailWord_709640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709727 : List Nat := [1, 1, 2, 3, 1, 1, 7, 5]
def baseStart_709727 : Nat := 118140960795 + 709727 * 2 ^ 59
def prefixEnd_709727 : Nat := 4983230072969 + 3 ^ 40 * 709727 * 2
def baseEnd_709727 : Nat := 53989790292392581266449

theorem tailTrace_709727 : CollatzResearch.WordTrace tailWord_709727 prefixEnd_709727 53989790292392581266449 := by
  unfold tailWord_709727
  simp only [CollatzResearch.WordTrace]
  refine ⟨25885870299787765566551435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17257246866525177044367623 25885870299787765566551435)
  ·
    refine ⟨38828805449681648349827153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25885870299787765566551435 38828805449681648349827153)
    ·
      refine ⟨29121604087261236262370365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38828805449681648349827153 29121604087261236262370365)
      ·
        refine ⟨10920601532722963598388887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29121604087261236262370365 10920601532722963598388887)
        ·
          refine ⟨16380902299084445397583331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10920601532722963598388887 16380902299084445397583331)
          ·
            refine ⟨24571353448626668096374997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16380902299084445397583331 24571353448626668096374997)
            ·
              refine ⟨575891096452187533508789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24571353448626668096374997 575891096452187533508789)
              ·
                refine ⟨53989790292392581266449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 575891096452187533508789 53989790292392581266449)
                ·
                  rfl

theorem cell21_709727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 5].length) (baseStart_709727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709727 prefixEnd_709727 := by exact prefixLift 709727
  have htrace : WordTrace (prefixWord ++ tailWord_709727) baseStart_709727 baseEnd_709727 := by
    simpa [prefixWord, tailWord_709727, baseEnd_709727] using wordTrace_append hprefix tailTrace_709727
  have hstable : (prefixWord ++ tailWord_709727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709727).length < 2 ^ (prefixWord ++ tailWord_709727).sum := by decide
  have hdescent : baseEnd_709727 < baseStart_709727 := by decide
  rcases family_descends (prefixWord ++ tailWord_709727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709772 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_709772 : Nat := 118140960795 + 709772 * 2 ^ 59
def prefixEnd_709772 : Nat := 4983230072969 + 3 ^ 40 * 709772 * 2
def baseEnd_709772 : Nat := 161979640490267665549255

theorem tailTrace_709772 : CollatzResearch.WordTrace tailWord_709772 prefixEnd_709772 161979640490267665549255 := by
  unfold tailWord_709772
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943755792312369125969785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17258341056416492167959713 12943755792312369125969785)
  ·
    refine ⟨9707816844234276844477339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12943755792312369125969785 9707816844234276844477339)
    ·
      refine ⟨14561725266351415266716009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9707816844234276844477339 14561725266351415266716009)
      ·
        refine ⟨10921293949763561450037007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14561725266351415266716009 10921293949763561450037007)
        ·
          refine ⟨16381940924645342175055511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10921293949763561450037007 16381940924645342175055511)
          ·
            refine ⟨24572911386968013262583267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16381940924645342175055511 24572911386968013262583267)
            ·
              refine ⟨36859367080452019893874901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24572911386968013262583267 36859367080452019893874901)
              ·
                refine ⟨863891415948094216262693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36859367080452019893874901 863891415948094216262693)
                ·
                  refine ⟨161979640490267665549255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 863891415948094216262693 161979640490267665549255)
                  ·
                    rfl

theorem cell21_709772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_709772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709772 prefixEnd_709772 := by exact prefixLift 709772
  have htrace : WordTrace (prefixWord ++ tailWord_709772) baseStart_709772 baseEnd_709772 := by
    simpa [prefixWord, tailWord_709772, baseEnd_709772] using wordTrace_append hprefix tailTrace_709772
  have hstable : (prefixWord ++ tailWord_709772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709772).length < 2 ^ (prefixWord ++ tailWord_709772).sum := by decide
  have hdescent : baseEnd_709772 < baseStart_709772 := by decide
  rcases family_descends (prefixWord ++ tailWord_709772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709868 : List Nat := [2, 2, 1, 1, 2, 6, 2, 2, 3]
def baseStart_709868 : Nat := 118140960795 + 709868 * 2 ^ 59
def prefixEnd_709868 : Nat := 4983230072969 + 3 ^ 40 * 709868 * 2
def baseEnd_709868 : Nat := 162001548998192831949059

theorem tailTrace_709868 : CollatzResearch.WordTrace tailWord_709868 prefixEnd_709868 162001548998192831949059 := by
  unfold tailWord_709868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12945506496138473323717129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17260675328184631098289505 12945506496138473323717129)
  ·
    refine ⟨9709129872103854992787847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12945506496138473323717129 9709129872103854992787847)
    ·
      refine ⟨14563694808155782489181771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9709129872103854992787847 14563694808155782489181771)
      ·
        refine ⟨21845542212233673733772657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14563694808155782489181771 21845542212233673733772657)
        ·
          refine ⟨16384156659175255300329493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21845542212233673733772657 16384156659175255300329493)
          ·
            refine ⟨768007343398840092202945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16384156659175255300329493 768007343398840092202945)
            ·
              refine ⟨576005507549130069152209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768007343398840092202945 576005507549130069152209)
              ·
                refine ⟨432004130661847551864157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576005507549130069152209 432004130661847551864157)
                ·
                  refine ⟨162001548998192831949059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432004130661847551864157 162001548998192831949059)
                  ·
                    rfl

theorem cell21_709868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_709868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709868 prefixEnd_709868 := by exact prefixLift 709868
  have htrace : WordTrace (prefixWord ++ tailWord_709868) baseStart_709868 baseEnd_709868 := by
    simpa [prefixWord, tailWord_709868, baseEnd_709868] using wordTrace_append hprefix tailTrace_709868
  have hstable : (prefixWord ++ tailWord_709868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709868).length < 2 ^ (prefixWord ++ tailWord_709868).sum := by decide
  have hdescent : baseEnd_709868 < baseStart_709868 := by decide
  rcases family_descends (prefixWord ++ tailWord_709868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709893 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 5]
def baseStart_709893 : Nat := 118140960795 + 709893 * 2 ^ 59
def prefixEnd_709893 : Nat := 4983230072969 + 3 ^ 40 * 709893 * 2
def baseEnd_709893 : Nat := 162007254338798344032341

theorem tailTrace_709893 : CollatzResearch.WordTrace tailWord_709893 prefixEnd_709893 162007254338798344032341 := by
  unfold tailWord_709893
  simp only [CollatzResearch.WordTrace]
  refine ⟨25891924817186375917094333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17261283211457583944729555 25891924817186375917094333)
  ·
    refine ⟨9709471806444890968910375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25891924817186375917094333 9709471806444890968910375)
    ·
      refine ⟨14564207709667336453365563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9709471806444890968910375 14564207709667336453365563)
      ·
        refine ⟨21846311564501004680048345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14564207709667336453365563 21846311564501004680048345)
        ·
          refine ⟨16384733673375753510036259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21846311564501004680048345 16384733673375753510036259)
          ·
            refine ⟨24577100510063630265054389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16384733673375753510036259 24577100510063630265054389)
            ·
              refine ⟨2304103172818465337348849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24577100510063630265054389 2304103172818465337348849)
              ·
                refine ⟨1728077379613849003011637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2304103172818465337348849 1728077379613849003011637)
                ·
                  refine ⟨162007254338798344032341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1728077379613849003011637 162007254338798344032341)
                  ·
                    rfl

theorem cell21_709893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_709893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709893 prefixEnd_709893 := by exact prefixLift 709893
  have htrace : WordTrace (prefixWord ++ tailWord_709893) baseStart_709893 baseEnd_709893 := by
    simpa [prefixWord, tailWord_709893, baseEnd_709893] using wordTrace_append hprefix tailTrace_709893
  have hstable : (prefixWord ++ tailWord_709893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709893).length < 2 ^ (prefixWord ++ tailWord_709893).sum := by decide
  have hdescent : baseEnd_709893 < baseStart_709893 := by decide
  rcases family_descends (prefixWord ++ tailWord_709893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709896 : List Nat := [2, 1, 3, 2, 4, 1, 3, 5]
def baseStart_709896 : Nat := 118140960795 + 709896 * 2 ^ 59
def prefixEnd_709896 : Nat := 4983230072969 + 3 ^ 40 * 709896 * 2
def baseEnd_709896 : Nat := 54002646326557001827445

theorem tailTrace_709896 : CollatzResearch.WordTrace tailWord_709896 prefixEnd_709896 54002646326557001827445 := by
  unfold tailWord_709896
  simp only [CollatzResearch.WordTrace]
  refine ⟨12946017118087753714726771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17261356157450338286302361 12946017118087753714726771)
  ·
    refine ⟨19419025677131630572090157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12946017118087753714726771 19419025677131630572090157)
    ·
      refine ⟨7282134628924361464533809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19419025677131630572090157 7282134628924361464533809)
      ·
        refine ⟨5461600971693271098400357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7282134628924361464533809 5461600971693271098400357)
        ·
          refine ⟨1024050182192488330950067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5461600971693271098400357 1024050182192488330950067)
          ·
            refine ⟨1536075273288732496425101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024050182192488330950067 1536075273288732496425101)
            ·
              refine ⟨576028227483274686159413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1536075273288732496425101 576028227483274686159413)
              ·
                refine ⟨54002646326557001827445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 576028227483274686159413 54002646326557001827445)
                ·
                  rfl

theorem cell21_709896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_709896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709896 prefixEnd_709896 := by exact prefixLift 709896
  have htrace : WordTrace (prefixWord ++ tailWord_709896) baseStart_709896 baseEnd_709896 := by
    simpa [prefixWord, tailWord_709896, baseEnd_709896] using wordTrace_append hprefix tailTrace_709896
  have hstable : (prefixWord ++ tailWord_709896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709896).length < 2 ^ (prefixWord ++ tailWord_709896).sum := by decide
  have hdescent : baseEnd_709896 < baseStart_709896 := by decide
  rcases family_descends (prefixWord ++ tailWord_709896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709924 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_709924 : Nat := 118140960795 + 709924 * 2 ^ 59
def prefixEnd_709924 : Nat := 4983230072969 + 3 ^ 40 * 709924 * 2
def baseEnd_709924 : Nat := 162014328961149179015611

theorem tailTrace_709924 : CollatzResearch.WordTrace tailWord_709924 prefixEnd_709924 162014328961149179015611 := by
  unfold tailWord_709924
  simp only [CollatzResearch.WordTrace]
  refine ⟨12946527740037034105736413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17262036986716045474315217 12946527740037034105736413)
  ·
    refine ⟨4854947902513887789651155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12946527740037034105736413 4854947902513887789651155)
    ·
      refine ⟨7282421853770831684476733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4854947902513887789651155 7282421853770831684476733)
      ·
        refine ⟨2730908195164061881678775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7282421853770831684476733 2730908195164061881678775)
        ·
          refine ⟨4096362292746092822518163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730908195164061881678775 4096362292746092822518163)
          ·
            refine ⟨6144543439119139233777245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096362292746092822518163 6144543439119139233777245)
            ·
              refine ⟨2304203789669677212666467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6144543439119139233777245 2304203789669677212666467)
              ·
                refine ⟨3456305684504515818999701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304203789669677212666467 3456305684504515818999701)
                ·
                  refine ⟨162014328961149179015611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3456305684504515818999701 162014328961149179015611)
                  ·
                    rfl

theorem cell21_709924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_709924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_709924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_709924 prefixEnd_709924 := by exact prefixLift 709924
  have htrace : WordTrace (prefixWord ++ tailWord_709924) baseStart_709924 baseEnd_709924 := by
    simpa [prefixWord, tailWord_709924, baseEnd_709924] using wordTrace_append hprefix tailTrace_709924
  have hstable : (prefixWord ++ tailWord_709924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709924).length < 2 ^ (prefixWord ++ tailWord_709924).sum := by decide
  have hdescent : baseEnd_709924 < baseStart_709924 := by decide
  rcases family_descends (prefixWord ++ tailWord_709924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710000 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_710000 : Nat := 118140960795 + 710000 * 2 ^ 59
def prefixEnd_710000 : Nat := 4983230072969 + 3 ^ 40 * 710000 * 2
def baseEnd_710000 : Nat := 162031673196589935748789

theorem tailTrace_710000 : CollatzResearch.WordTrace tailWord_710000 prefixEnd_710000 162031673196589935748789 := by
  unfold tailWord_710000
  simp only [CollatzResearch.WordTrace]
  refine ⟨12947913713899366595619727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17263884951865822127492969 12947913713899366595619727)
  ·
    refine ⟨19421870570849049893429591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12947913713899366595619727 19421870570849049893429591)
    ·
      refine ⟨29132805856273574840144387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19421870570849049893429591 29132805856273574840144387)
      ·
        refine ⟨43699208784410362260216581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29132805856273574840144387 43699208784410362260216581)
        ·
          refine ⟨8193601647076942923790609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43699208784410362260216581 8193601647076942923790609)
          ·
            refine ⟨6145201235307707192842957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8193601647076942923790609 6145201235307707192842957)
            ·
              refine ⟨2304450463240390197316109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6145201235307707192842957 2304450463240390197316109)
              ·
                refine ⟨864168923715146323993541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2304450463240390197316109 864168923715146323993541)
                ·
                  refine ⟨162031673196589935748789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864168923715146323993541 162031673196589935748789)
                  ·
                    rfl

theorem cell21_710000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_710000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710000 prefixEnd_710000 := by exact prefixLift 710000
  have htrace : WordTrace (prefixWord ++ tailWord_710000) baseStart_710000 baseEnd_710000 := by
    simpa [prefixWord, tailWord_710000, baseEnd_710000] using wordTrace_append hprefix tailTrace_710000
  have hstable : (prefixWord ++ tailWord_710000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710000).length < 2 ^ (prefixWord ++ tailWord_710000).sum := by decide
  have hdescent : baseEnd_710000 < baseStart_710000 := by decide
  rcases family_descends (prefixWord ++ tailWord_710000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710082 : List Nat := [3, 5, 2, 1, 1, 1, 8]
def baseStart_710082 : Nat := 118140960795 + 710082 * 2 ^ 59
def prefixEnd_710082 : Nat := 4983230072969 + 3 ^ 40 * 710082 * 2
def baseEnd_710082 : Nat := 18005598523752890597995

theorem tailTrace_710082 : CollatzResearch.WordTrace tailWord_710082 prefixEnd_710082 18005598523752890597995 := by
  unfold tailWord_710082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474704553375415298931125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17265878809001107463816333 6474704553375415298931125)
  ·
    refine ⟨607003551878945184274793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6474704553375415298931125 607003551878945184274793)
    ·
      refine ⟨455252663909208888206095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 607003551878945184274793 455252663909208888206095)
      ·
        refine ⟨682878995863813332309143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455252663909208888206095 682878995863813332309143)
        ·
          refine ⟨1024318493795719998463715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682878995863813332309143 1024318493795719998463715)
          ·
            refine ⟨1536477740693579997695573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024318493795719998463715 1536477740693579997695573)
            ·
              refine ⟨18005598523752890597995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1536477740693579997695573 18005598523752890597995)
              ·
                rfl

theorem cell21_710082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 8].length) (baseStart_710082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710082 prefixEnd_710082 := by exact prefixLift 710082
  have htrace : WordTrace (prefixWord ++ tailWord_710082) baseStart_710082 baseEnd_710082 := by
    simpa [prefixWord, tailWord_710082, baseEnd_710082] using wordTrace_append hprefix tailTrace_710082
  have hstable : (prefixWord ++ tailWord_710082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710082).length < 2 ^ (prefixWord ++ tailWord_710082).sum := by decide
  have hdescent : baseEnd_710082 < baseStart_710082 := by decide
  rcases family_descends (prefixWord ++ tailWord_710082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710090 : List Nat := [3, 1, 2, 1, 2, 4, 8]
def baseStart_710090 : Nat := 118140960795 + 710090 * 2 ^ 59
def prefixEnd_710090 : Nat := 4983230072969 + 3 ^ 40 * 710090 * 2
def baseEnd_710090 : Nat := 18005801380307753249845

theorem tailTrace_710090 : CollatzResearch.WordTrace tailWord_710090 prefixEnd_710090 18005801380307753249845 := by
  unfold tailWord_710090
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474777499368169640503931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17266073331648452374677149 6474777499368169640503931)
  ·
    refine ⟨9712166249052254460755897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6474777499368169640503931 9712166249052254460755897)
    ·
      refine ⟨7284124686789190845566923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9712166249052254460755897 7284124686789190845566923)
      ·
        refine ⟨10926187030183786268350385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7284124686789190845566923 10926187030183786268350385)
        ·
          refine ⟨8194640272637839701262789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10926187030183786268350385 8194640272637839701262789)
          ·
            refine ⟨1536495051119594943986773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8194640272637839701262789 1536495051119594943986773)
            ·
              refine ⟨18005801380307753249845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1536495051119594943986773 18005801380307753249845)
              ·
                rfl

theorem cell21_710090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 8].length) (baseStart_710090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710090 prefixEnd_710090 := by exact prefixLift 710090
  have htrace : WordTrace (prefixWord ++ tailWord_710090) baseStart_710090 baseEnd_710090 := by
    simpa [prefixWord, tailWord_710090, baseEnd_710090] using wordTrace_append hprefix tailTrace_710090
  have hstable : (prefixWord ++ tailWord_710090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710090).length < 2 ^ (prefixWord ++ tailWord_710090).sum := by decide
  have hdescent : baseEnd_710090 < baseStart_710090 := by decide
  rcases family_descends (prefixWord ++ tailWord_710090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710155 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 5]
def baseStart_710155 : Nat := 118140960795 + 710155 * 2 ^ 59
def prefixEnd_710155 : Nat := 4983230072969 + 3 ^ 40 * 710155 * 2
def baseEnd_710155 : Nat := 162067046308344110665139

theorem tailTrace_710155 : CollatzResearch.WordTrace tailWord_710155 prefixEnd_710155 162067046308344110665139 := by
  unfold tailWord_710155
  simp only [CollatzResearch.WordTrace]
  refine ⟨25901480742237194663131919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17267653828158129775421279 25901480742237194663131919)
  ·
    refine ⟨38852221113355791994697879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25901480742237194663131919 38852221113355791994697879)
    ·
      refine ⟨58278331670033687992046819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38852221113355791994697879 58278331670033687992046819)
      ·
        refine ⟨87417497505050531988070229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58278331670033687992046819 87417497505050531988070229)
        ·
          refine ⟨512211899443655460867599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 87417497505050531988070229 512211899443655460867599)
          ·
            refine ⟨768317849165483191301399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512211899443655460867599 768317849165483191301399)
            ·
              refine ⟨1152476773748224786952099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768317849165483191301399 1152476773748224786952099)
              ·
                refine ⟨1728715160622337180428149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152476773748224786952099 1728715160622337180428149)
                ·
                  refine ⟨162067046308344110665139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1728715160622337180428149 162067046308344110665139)
                  ·
                    rfl

theorem cell21_710155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 5].length) (baseStart_710155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710155 prefixEnd_710155 := by exact prefixLift 710155
  have htrace : WordTrace (prefixWord ++ tailWord_710155) baseStart_710155 baseEnd_710155 := by
    simpa [prefixWord, tailWord_710155, baseEnd_710155] using wordTrace_append hprefix tailTrace_710155
  have hstable : (prefixWord ++ tailWord_710155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710155).length < 2 ^ (prefixWord ++ tailWord_710155).sum := by decide
  have hdescent : baseEnd_710155 < baseStart_710155 := by decide
  rcases family_descends (prefixWord ++ tailWord_710155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710228 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_710228 : Nat := 118140960795 + 710228 * 2 ^ 59
def prefixEnd_710228 : Nat := 4983230072969 + 3 ^ 40 * 710228 * 2
def baseEnd_710228 : Nat := 162083705902912205948323

theorem tailTrace_710228 : CollatzResearch.WordTrace tailWord_710228 prefixEnd_710228 162083705902912205948323 := by
  unfold tailWord_710228
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952071635486364065269669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17269428847315152087026225 12952071635486364065269669)
  ·
    refine ⟨2428513431653693262238063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12952071635486364065269669 2428513431653693262238063)
    ·
      refine ⟨3642770147480539893357095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428513431653693262238063 3642770147480539893357095)
      ·
        refine ⟨5464155221220809840035643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3642770147480539893357095 5464155221220809840035643)
        ·
          refine ⟨8196232831831214760053465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464155221220809840035643 8196232831831214760053465)
          ·
            refine ⟨6147174623873411070040099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8196232831831214760053465 6147174623873411070040099)
            ·
              refine ⟨9220761935810116605060149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147174623873411070040099 9220761935810116605060149)
              ·
                refine ⟨864446431482198431724389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9220761935810116605060149 864446431482198431724389)
                ·
                  refine ⟨162083705902912205948323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864446431482198431724389 162083705902912205948323)
                  ·
                    rfl

theorem cell21_710228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_710228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710228 prefixEnd_710228 := by exact prefixLift 710228
  have htrace : WordTrace (prefixWord ++ tailWord_710228) baseStart_710228 baseEnd_710228 := by
    simpa [prefixWord, tailWord_710228, baseEnd_710228] using wordTrace_append hprefix tailTrace_710228
  have hstable : (prefixWord ++ tailWord_710228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710228).length < 2 ^ (prefixWord ++ tailWord_710228).sum := by decide
  have hdescent : baseEnd_710228 < baseStart_710228 := by decide
  rcases family_descends (prefixWord ++ tailWord_710228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710262 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_710262 : Nat := 118140960795 + 710262 * 2 ^ 59
def prefixEnd_710262 : Nat := 4983230072969 + 3 ^ 40 * 710262 * 2
def baseEnd_710262 : Nat := 162091465166135702381587

theorem tailTrace_710262 : CollatzResearch.WordTrace tailWord_710262 prefixEnd_710262 162091465166135702381587 := by
  unfold tailWord_710262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619086459553096996079815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17270255568566367958184693 1619086459553096996079815)
  ·
    refine ⟨2428629689329645494119723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1619086459553096996079815 2428629689329645494119723)
    ·
      refine ⟨3642944533994468241179585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428629689329645494119723 3642944533994468241179585)
      ·
        refine ⟨2732208400495851180884689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3642944533994468241179585 2732208400495851180884689)
        ·
          refine ⟨2049156300371888385663517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732208400495851180884689 2049156300371888385663517)
          ·
            refine ⟨768433612639458144623819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2049156300371888385663517 768433612639458144623819)
            ·
              refine ⟨1152650418959187216935729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768433612639458144623819 1152650418959187216935729)
              ·
                refine ⟨864487814219390412701797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152650418959187216935729 864487814219390412701797)
                ·
                  refine ⟨162091465166135702381587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864487814219390412701797 162091465166135702381587)
                  ·
                    rfl

theorem cell21_710262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_710262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710262 prefixEnd_710262 := by exact prefixLift 710262
  have htrace : WordTrace (prefixWord ++ tailWord_710262) baseStart_710262 baseEnd_710262 := by
    simpa [prefixWord, tailWord_710262, baseEnd_710262] using wordTrace_append hprefix tailTrace_710262
  have hstable : (prefixWord ++ tailWord_710262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710262).length < 2 ^ (prefixWord ++ tailWord_710262).sum := by decide
  have hdescent : baseEnd_710262 < baseStart_710262 := by decide
  rcases family_descends (prefixWord ++ tailWord_710262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710273 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 5]
def baseStart_710273 : Nat := 118140960795 + 710273 * 2 ^ 59
def prefixEnd_710273 : Nat := 4983230072969 + 3 ^ 40 * 710273 * 2
def baseEnd_710273 : Nat := 162093975516002127698231

theorem tailTrace_710273 : CollatzResearch.WordTrace tailWord_710273 prefixEnd_710273 162093975516002127698231 := by
  unfold tailWord_710273
  simp only [CollatzResearch.WordTrace]
  refine ⟨25905784555809700815927473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17270523037206467210618315 25905784555809700815927473)
  ·
    refine ⟨19429338416857275611945605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25905784555809700815927473 19429338416857275611945605)
    ·
      refine ⟨3643000953160739177239801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19429338416857275611945605 3643000953160739177239801)
      ·
        refine ⟨2732250714870554382929851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3643000953160739177239801 2732250714870554382929851)
        ·
          refine ⟨4098376072305831574394777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732250714870554382929851 4098376072305831574394777)
          ·
            refine ⟨3073782054229373680796083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4098376072305831574394777 3073782054229373680796083)
            ·
              refine ⟨4610673081344060521194125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3073782054229373680796083 4610673081344060521194125)
              ·
                refine ⟨1729002405504022695447797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4610673081344060521194125 1729002405504022695447797)
                ·
                  refine ⟨162093975516002127698231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729002405504022695447797 162093975516002127698231)
                  ·
                    rfl

theorem cell21_710273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_710273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710273 prefixEnd_710273 := by exact prefixLift 710273
  have htrace : WordTrace (prefixWord ++ tailWord_710273) baseStart_710273 baseEnd_710273 := by
    simpa [prefixWord, tailWord_710273, baseEnd_710273] using wordTrace_append hprefix tailTrace_710273
  have hstable : (prefixWord ++ tailWord_710273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710273).length < 2 ^ (prefixWord ++ tailWord_710273).sum := by decide
  have hdescent : baseEnd_710273 < baseStart_710273 := by decide
  rcases family_descends (prefixWord ++ tailWord_710273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710476 : List Nat := [2, 2, 1, 3, 5, 1, 1, 3, 3]
def baseStart_710476 : Nat := 118140960795 + 710476 * 2 ^ 59
def prefixEnd_710476 : Nat := 4983230072969 + 3 ^ 40 * 710476 * 2
def baseEnd_710476 : Nat := 162140302881718885814483

theorem tailTrace_710476 : CollatzResearch.WordTrace tailWord_710476 prefixEnd_710476 162140302881718885814483 := by
  unfold tailWord_710476
  simp only [CollatzResearch.WordTrace]
  refine ⟨12956594287037133242783641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17275459049382844323711521 12956594287037133242783641)
  ·
    refine ⟨9717445715277849932087731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12956594287037133242783641 9717445715277849932087731)
    ·
      refine ⟨14576168572916774898131597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9717445715277849932087731 14576168572916774898131597)
      ·
        refine ⟨5466063214843790586799349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14576168572916774898131597 5466063214843790586799349)
        ·
          refine ⟨512443426391605367512439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5466063214843790586799349 512443426391605367512439)
          ·
            refine ⟨768665139587408051268659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512443426391605367512439 768665139587408051268659)
            ·
              refine ⟨1152997709381112076902989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768665139587408051268659 1152997709381112076902989)
              ·
                refine ⟨432374141017917028838621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1152997709381112076902989 432374141017917028838621)
                ·
                  refine ⟨162140302881718885814483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432374141017917028838621 162140302881718885814483)
                  ·
                    rfl

theorem cell21_710476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_710476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710476 prefixEnd_710476 := by exact prefixLift 710476
  have htrace : WordTrace (prefixWord ++ tailWord_710476) baseStart_710476 baseEnd_710476 := by
    simpa [prefixWord, tailWord_710476, baseEnd_710476] using wordTrace_append hprefix tailTrace_710476
  have hstable : (prefixWord ++ tailWord_710476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710476).length < 2 ^ (prefixWord ++ tailWord_710476).sum := by decide
  have hdescent : baseEnd_710476 < baseStart_710476 := by decide
  rcases family_descends (prefixWord ++ tailWord_710476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710487 : List Nat := [1, 1, 3, 2, 6, 1, 7]
def baseStart_710487 : Nat := 118140960795 + 710487 * 2 ^ 59
def prefixEnd_710487 : Nat := 4983230072969 + 3 ^ 40 * 710487 * 2
def baseEnd_710487 : Nat := 18015868136842812347903

theorem tailTrace_710487 : CollatzResearch.WordTrace tailWord_710487 prefixEnd_710487 18015868136842812347903 := by
  unfold tailWord_710487
  simp only [CollatzResearch.WordTrace]
  refine ⟨25913589777034415364217715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17275726518022943576145143 25913589777034415364217715)
  ·
    refine ⟨38870384665551623046326573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25913589777034415364217715 38870384665551623046326573)
    ·
      refine ⟨14576394249581858642372465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38870384665551623046326573 14576394249581858642372465)
      ·
        refine ⟨10932295687186393981779349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14576394249581858642372465 10932295687186393981779349)
        ·
          refine ⟨512451360336862217895907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10932295687186393981779349 512451360336862217895907)
          ·
            refine ⟨768677040505293326843861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512451360336862217895907 768677040505293326843861)
            ·
              refine ⟨18015868136842812347903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 768677040505293326843861 18015868136842812347903)
              ·
                rfl

theorem cell21_710487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 7].length) (baseStart_710487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710487 prefixEnd_710487 := by exact prefixLift 710487
  have htrace : WordTrace (prefixWord ++ tailWord_710487) baseStart_710487 baseEnd_710487 := by
    simpa [prefixWord, tailWord_710487, baseEnd_710487] using wordTrace_append hprefix tailTrace_710487
  have hstable : (prefixWord ++ tailWord_710487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710487).length < 2 ^ (prefixWord ++ tailWord_710487).sum := by decide
  have hdescent : baseEnd_710487 < baseStart_710487 := by decide
  rcases family_descends (prefixWord ++ tailWord_710487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710546 : List Nat := [3, 2, 3, 2, 1, 10]
def baseStart_710546 : Nat := 118140960795 + 710546 * 2 ^ 59
def prefixEnd_710546 : Nat := 4983230072969 + 3 ^ 40 * 710546 * 2
def baseEnd_710546 : Nat := 6005788067978308135099

theorem tailTrace_710546 : CollatzResearch.WordTrace tailWord_710546 prefixEnd_710546 6005788067978308135099 := by
  unfold tailWord_710546
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478935420955167110153873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17277161122547112293743661 6478935420955167110153873)
  ·
    refine ⟨4859201565716375332615405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6478935420955167110153873 4859201565716375332615405)
    ·
      refine ⟨1822200587143640749730777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4859201565716375332615405 1822200587143640749730777)
      ·
        refine ⟨1366650440357730562298083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1822200587143640749730777 1366650440357730562298083)
        ·
          refine ⟨2049975660536595843447125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1366650440357730562298083 2049975660536595843447125)
          ·
            refine ⟨6005788067978308135099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2049975660536595843447125 6005788067978308135099)
            ·
              rfl

theorem cell21_710546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 10].length) (baseStart_710546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710546 prefixEnd_710546 := by exact prefixLift 710546
  have htrace : WordTrace (prefixWord ++ tailWord_710546) baseStart_710546 baseEnd_710546 := by
    simpa [prefixWord, tailWord_710546, baseEnd_710546] using wordTrace_append hprefix tailTrace_710546
  have hstable : (prefixWord ++ tailWord_710546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710546).length < 2 ^ (prefixWord ++ tailWord_710546).sum := by decide
  have hdescent : baseEnd_710546 < baseStart_710546 := by decide
  rcases family_descends (prefixWord ++ tailWord_710546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710560 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_710560 : Nat := 118140960795 + 710560 * 2 ^ 59
def prefixEnd_710560 : Nat := 4983230072969 + 3 ^ 40 * 710560 * 2
def baseEnd_710560 : Nat := 162159472826153406414311

theorem tailTrace_710560 : CollatzResearch.WordTrace tailWord_710560 prefixEnd_710560 162159472826153406414311 := by
  unfold tailWord_710560
  simp only [CollatzResearch.WordTrace]
  refine ⟨12958126152884974415812567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17277501537179965887750089 12958126152884974415812567)
  ·
    refine ⟨19437189229327461623718851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12958126152884974415812567 19437189229327461623718851)
    ·
      refine ⟨29155783843991192435578277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19437189229327461623718851 29155783843991192435578277)
      ·
        refine ⟨5466709470748348581670927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29155783843991192435578277 5466709470748348581670927)
        ·
          refine ⟨8200064206122522872506391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5466709470748348581670927 8200064206122522872506391)
          ·
            refine ⟨12300096309183784308759587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8200064206122522872506391 12300096309183784308759587)
            ·
              refine ⟨18450144463775676463139381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12300096309183784308759587 18450144463775676463139381)
              ·
                refine ⟨1729701043478969668419317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18450144463775676463139381 1729701043478969668419317)
                ·
                  refine ⟨162159472826153406414311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729701043478969668419317 162159472826153406414311)
                  ·
                    rfl

theorem cell21_710560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_710560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710560 prefixEnd_710560 := by exact prefixLift 710560
  have htrace : WordTrace (prefixWord ++ tailWord_710560) baseStart_710560 baseEnd_710560 := by
    simpa [prefixWord, tailWord_710560, baseEnd_710560] using wordTrace_append hprefix tailTrace_710560
  have hstable : (prefixWord ++ tailWord_710560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710560).length < 2 ^ (prefixWord ++ tailWord_710560).sum := by decide
  have hdescent : baseEnd_710560 < baseStart_710560 := by decide
  rcases family_descends (prefixWord ++ tailWord_710560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710577 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 5]
def baseStart_710577 : Nat := 118140960795 + 710577 * 2 ^ 59
def prefixEnd_710577 : Nat := 4983230072969 + 3 ^ 40 * 710577 * 2
def baseEnd_710577 : Nat := 162163352457765154630943

theorem tailTrace_710577 : CollatzResearch.WordTrace tailWord_710577 prefixEnd_710577 162163352457765154630943 := by
  unfold tailWord_710577
  simp only [CollatzResearch.WordTrace]
  refine ⟨25916872346708360734993985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17277914897805573823329323 25916872346708360734993985)
  ·
    refine ⟨19437654260031270551245489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25916872346708360734993985 19437654260031270551245489)
    ·
      refine ⟨14578240695023452913434117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19437654260031270551245489 14578240695023452913434117)
      ·
        refine ⟨2733420130316897421268897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14578240695023452913434117 2733420130316897421268897)
        ·
          refine ⟨2050065097737673065951673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733420130316897421268897 2050065097737673065951673)
          ·
            refine ⟨1537548823303254799463755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2050065097737673065951673 1537548823303254799463755)
            ·
              refine ⟨2306323234954882199195633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537548823303254799463755 2306323234954882199195633)
              ·
                refine ⟨1729742426216161649396725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306323234954882199195633 1729742426216161649396725)
                ·
                  refine ⟨162163352457765154630943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729742426216161649396725 162163352457765154630943)
                  ·
                    rfl

theorem cell21_710577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_710577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710577 prefixEnd_710577 := by exact prefixLift 710577
  have htrace : WordTrace (prefixWord ++ tailWord_710577) baseStart_710577 baseEnd_710577 := by
    simpa [prefixWord, tailWord_710577, baseEnd_710577] using wordTrace_append hprefix tailTrace_710577
  have hstable : (prefixWord ++ tailWord_710577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710577).length < 2 ^ (prefixWord ++ tailWord_710577).sum := by decide
  have hdescent : baseEnd_710577 < baseStart_710577 := by decide
  rcases family_descends (prefixWord ++ tailWord_710577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710662 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_710662 : Nat := 118140960795 + 710662 * 2 ^ 59
def prefixEnd_710662 : Nat := 4983230072969 + 3 ^ 40 * 710662 * 2
def baseEnd_710662 : Nat := 162182750615823895714103

theorem tailTrace_710662 : CollatzResearch.WordTrace tailWord_710662 prefixEnd_710662 162182750615823895714103 := by
  unfold tailWord_710662
  simp only [CollatzResearch.WordTrace]
  refine ⟨809999142231263132869945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17279981700933613501225493 809999142231263132869945)
  ·
    refine ⟨607499356673447349652459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 809999142231263132869945 607499356673447349652459)
    ·
      refine ⟨911249035010171024478689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607499356673447349652459 911249035010171024478689)
      ·
        refine ⟨683436776257628268359017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 911249035010171024478689 683436776257628268359017)
        ·
          refine ⟨512577582193221201269263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683436776257628268359017 512577582193221201269263)
          ·
            refine ⟨768866373289831801903895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512577582193221201269263 768866373289831801903895)
            ·
              refine ⟨1153299559934747702855843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768866373289831801903895 1153299559934747702855843)
              ·
                refine ⟨1729949339902121554283765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153299559934747702855843 1729949339902121554283765)
                ·
                  refine ⟨162182750615823895714103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1729949339902121554283765 162182750615823895714103)
                  ·
                    rfl

theorem cell21_710662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_710662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710662 prefixEnd_710662 := by exact prefixLift 710662
  have htrace : WordTrace (prefixWord ++ tailWord_710662) baseStart_710662 baseEnd_710662 := by
    simpa [prefixWord, tailWord_710662, baseEnd_710662] using wordTrace_append hprefix tailTrace_710662
  have hstable : (prefixWord ++ tailWord_710662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710662).length < 2 ^ (prefixWord ++ tailWord_710662).sum := by decide
  have hdescent : baseEnd_710662 < baseStart_710662 := by decide
  rcases family_descends (prefixWord ++ tailWord_710662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710667 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 4]
def baseStart_710667 : Nat := 118140960795 + 710667 * 2 ^ 59
def prefixEnd_710667 : Nat := 4983230072969 + 3 ^ 40 * 710667 * 2
def baseEnd_710667 : Nat := 162183891683944998130759

theorem tailTrace_710667 : CollatzResearch.WordTrace tailWord_710667 prefixEnd_710667 162183891683944998130759 := by
  unfold tailWord_710667
  simp only [CollatzResearch.WordTrace]
  refine ⟨25920154916382306105770255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17280103277588204070513503 25920154916382306105770255)
  ·
    refine ⟨38880232374573459158655383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25920154916382306105770255 38880232374573459158655383)
    ·
      refine ⟨58320348561860188737983075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38880232374573459158655383 58320348561860188737983075)
      ·
        refine ⟨87480522842790283106974613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58320348561860188737983075 87480522842790283106974613)
        ·
          refine ⟨4100649508255794520639435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87480522842790283106974613 4100649508255794520639435)
          ·
            refine ⟨6150974262383691780959153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100649508255794520639435 6150974262383691780959153)
            ·
              refine ⟨4613230696787768835719365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6150974262383691780959153 4613230696787768835719365)
              ·
                refine ⟨864980755647706656697381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4613230696787768835719365 864980755647706656697381)
                ·
                  refine ⟨162183891683944998130759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864980755647706656697381 162183891683944998130759)
                  ·
                    rfl

theorem cell21_710667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 4].length) (baseStart_710667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710667 prefixEnd_710667 := by exact prefixLift 710667
  have htrace : WordTrace (prefixWord ++ tailWord_710667) baseStart_710667 baseEnd_710667 := by
    simpa [prefixWord, tailWord_710667, baseEnd_710667] using wordTrace_append hprefix tailTrace_710667
  have hstable : (prefixWord ++ tailWord_710667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710667).length < 2 ^ (prefixWord ++ tailWord_710667).sum := by decide
  have hdescent : baseEnd_710667 < baseStart_710667 := by decide
  rcases family_descends (prefixWord ++ tailWord_710667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710676 : List Nat := [2, 4, 3, 2, 2, 1, 2, 1, 4]
def baseStart_710676 : Nat := 118140960795 + 710676 * 2 ^ 59
def prefixEnd_710676 : Nat := 4983230072969 + 3 ^ 40 * 710676 * 2
def baseEnd_710676 : Nat := 162185945606562982480741

theorem tailTrace_710676 : CollatzResearch.WordTrace tailWord_710676 prefixEnd_710676 162185945606562982480741 := by
  unfold tailWord_710676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12960241586674850321423941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17280322115566467095231921 12960241586674850321423941)
  ·
    refine ⟨2430045297501534435266989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12960241586674850321423941 2430045297501534435266989)
    ·
      refine ⟨911266986563075413225121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2430045297501534435266989 911266986563075413225121)
      ·
        refine ⟨683450239922306559918841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 911266986563075413225121 683450239922306559918841)
        ·
          refine ⟨512587679941729919939131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683450239922306559918841 512587679941729919939131)
          ·
            refine ⟨768881519912594879908697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512587679941729919939131 768881519912594879908697)
            ·
              refine ⟨576661139934446159931523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768881519912594879908697 576661139934446159931523)
              ·
                refine ⟨864991709901669239897285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576661139934446159931523 864991709901669239897285)
                ·
                  refine ⟨162185945606562982480741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 864991709901669239897285 162185945606562982480741)
                  ·
                    rfl

theorem cell21_710676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_710676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710676 prefixEnd_710676 := by exact prefixLift 710676
  have htrace : WordTrace (prefixWord ++ tailWord_710676) baseStart_710676 baseEnd_710676 := by
    simpa [prefixWord, tailWord_710676, baseEnd_710676] using wordTrace_append hprefix tailTrace_710676
  have hstable : (prefixWord ++ tailWord_710676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710676).length < 2 ^ (prefixWord ++ tailWord_710676).sum := by decide
  have hdescent : baseEnd_710676 < baseStart_710676 := by decide
  rcases family_descends (prefixWord ++ tailWord_710676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710684 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_710684 : Nat := 118140960795 + 710684 * 2 ^ 59
def prefixEnd_710684 : Nat := 4983230072969 + 3 ^ 40 * 710684 * 2
def baseEnd_710684 : Nat := 162187771315556746347391

theorem tailTrace_710684 : CollatzResearch.WordTrace tailWord_710684 prefixEnd_710684 162187771315556746347391 := by
  unfold tailWord_710684
  simp only [CollatzResearch.WordTrace]
  refine ⟨12960387478660359004569553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17280516638213812006092737 12960387478660359004569553)
  ·
    refine ⟨9720290608995269253427165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12960387478660359004569553 9720290608995269253427165)
    ·
      refine ⟨3645108978373225970035187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9720290608995269253427165 3645108978373225970035187)
      ·
        refine ⟨5467663467559838955052781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3645108978373225970035187 5467663467559838955052781)
        ·
          refine ⟨2050373800334939608144793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5467663467559838955052781 2050373800334939608144793)
          ·
            refine ⟨1537780350251204706108595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2050373800334939608144793 1537780350251204706108595)
            ·
              refine ⟨2306670525376807059162893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537780350251204706108595 2306670525376807059162893)
              ·
                refine ⟨865001447016302647186085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2306670525376807059162893 865001447016302647186085)
                ·
                  refine ⟨162187771315556746347391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865001447016302647186085 162187771315556746347391)
                  ·
                    rfl

theorem cell21_710684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_710684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710684 prefixEnd_710684 := by exact prefixLift 710684
  have htrace : WordTrace (prefixWord ++ tailWord_710684) baseStart_710684 baseEnd_710684 := by
    simpa [prefixWord, tailWord_710684, baseEnd_710684] using wordTrace_append hprefix tailTrace_710684
  have hstable : (prefixWord ++ tailWord_710684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710684).length < 2 ^ (prefixWord ++ tailWord_710684).sum := by decide
  have hdescent : baseEnd_710684 < baseStart_710684 := by decide
  rcases family_descends (prefixWord ++ tailWord_710684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710698 : List Nat := [3, 1, 4, 1, 2, 1, 2, 7]
def baseStart_710698 : Nat := 118140960795 + 710698 * 2 ^ 59
def prefixEnd_710698 : Nat := 4983230072969 + 3 ^ 40 * 710698 * 2
def baseEnd_710698 : Nat := 54063655435431944371343

theorem tailTrace_710698 : CollatzResearch.WordTrace tailWord_710698 prefixEnd_710698 54063655435431944371343 := by
  unfold tailWord_710698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6480321394817499600037187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17280857052846665600099165 6480321394817499600037187)
  ·
    refine ⟨9720482092226249400055781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6480321394817499600037187 9720482092226249400055781)
    ·
      refine ⟨1822590392292421762510459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9720482092226249400055781 1822590392292421762510459)
      ·
        refine ⟨2733885588438632643765689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822590392292421762510459 2733885588438632643765689)
        ·
          refine ⟨2050414191328974482824267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733885588438632643765689 2050414191328974482824267)
          ·
            refine ⟨3075621286993461724236401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050414191328974482824267 3075621286993461724236401)
            ·
              refine ⟨2306715965245096293177301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3075621286993461724236401 2306715965245096293177301)
              ·
                refine ⟨54063655435431944371343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2306715965245096293177301 54063655435431944371343)
                ·
                  rfl

theorem cell21_710698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_710698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710698 prefixEnd_710698 := by exact prefixLift 710698
  have htrace : WordTrace (prefixWord ++ tailWord_710698) baseStart_710698 baseEnd_710698 := by
    simpa [prefixWord, tailWord_710698, baseEnd_710698] using wordTrace_append hprefix tailTrace_710698
  have hstable : (prefixWord ++ tailWord_710698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710698).length < 2 ^ (prefixWord ++ tailWord_710698).sum := by decide
  have hdescent : baseEnd_710698 < baseStart_710698 := by decide
  rcases family_descends (prefixWord ++ tailWord_710698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710729 : List Nat := [1, 2, 1, 1, 2, 2, 5, 4, 3]
def baseStart_710729 : Nat := 118140960795 + 710729 * 2 ^ 59
def prefixEnd_710729 : Nat := 4983230072969 + 3 ^ 40 * 710729 * 2
def baseEnd_710729 : Nat := 162198040928646668097299

theorem tailTrace_710729 : CollatzResearch.WordTrace tailWord_710729 prefixEnd_710729 162198040928646668097299 := by
  unfold tailWord_710729
  simp only [CollatzResearch.WordTrace]
  refine ⟨25922416242157690694527241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17281610828105127129684827 25922416242157690694527241)
  ·
    refine ⟨19441812181618268020895431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25922416242157690694527241 19441812181618268020895431)
    ·
      refine ⟨29162718272427402031343147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19441812181618268020895431 29162718272427402031343147)
      ·
        refine ⟨43744077408641103047014721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29162718272427402031343147 43744077408641103047014721)
        ·
          refine ⟨32808058056480827285261041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43744077408641103047014721 32808058056480827285261041)
          ·
            refine ⟨24606043542360620463945781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32808058056480827285261041 24606043542360620463945781)
            ·
              refine ⟨2306816582096308168494917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24606043542360620463945781 2306816582096308168494917)
              ·
                refine ⟨432528109143057781592797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2306816582096308168494917 432528109143057781592797)
                ·
                  refine ⟨162198040928646668097299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432528109143057781592797 162198040928646668097299)
                  ·
                    rfl

theorem cell21_710729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_710729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710729 prefixEnd_710729 := by exact prefixLift 710729
  have htrace : WordTrace (prefixWord ++ tailWord_710729) baseStart_710729 baseEnd_710729 := by
    simpa [prefixWord, tailWord_710729, baseEnd_710729] using wordTrace_append hprefix tailTrace_710729
  have hstable : (prefixWord ++ tailWord_710729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710729).length < 2 ^ (prefixWord ++ tailWord_710729).sum := by decide
  have hdescent : baseEnd_710729 < baseStart_710729 := by decide
  rcases family_descends (prefixWord ++ tailWord_710729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710743 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 4]
def baseStart_710743 : Nat := 118140960795 + 710743 * 2 ^ 59
def prefixEnd_710743 : Nat := 4983230072969 + 3 ^ 40 * 710743 * 2
def baseEnd_710743 : Nat := 162201235919385754863937

theorem tailTrace_710743 : CollatzResearch.WordTrace tailWord_710743 prefixEnd_710743 162201235919385754863937 := by
  unfold tailWord_710743
  simp only [CollatzResearch.WordTrace]
  refine ⟨25922926864106971085536883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17281951242737980723691255 25922926864106971085536883)
  ·
    refine ⟨38884390296160456628305325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25922926864106971085536883 38884390296160456628305325)
    ·
      refine ⟨14581646361060171235614497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38884390296160456628305325 14581646361060171235614497)
      ·
        refine ⟨10936234770795128426710873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14581646361060171235614497 10936234770795128426710873)
        ·
          refine ⟨8202176078096346320033155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10936234770795128426710873 8202176078096346320033155)
          ·
            refine ⟨12303264117144519480049733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8202176078096346320033155 12303264117144519480049733)
            ·
              refine ⟨2306862021964597402509325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12303264117144519480049733 2306862021964597402509325)
              ·
                refine ⟨865073258236724025940997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2306862021964597402509325 865073258236724025940997)
                ·
                  refine ⟨162201235919385754863937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865073258236724025940997 162201235919385754863937)
                  ·
                    rfl

theorem cell21_710743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 4].length) (baseStart_710743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710743 prefixEnd_710743 := by exact prefixLift 710743
  have htrace : WordTrace (prefixWord ++ tailWord_710743) baseStart_710743 baseEnd_710743 := by
    simpa [prefixWord, tailWord_710743, baseEnd_710743] using wordTrace_append hprefix tailTrace_710743
  have hstable : (prefixWord ++ tailWord_710743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710743).length < 2 ^ (prefixWord ++ tailWord_710743).sum := by decide
  have hdescent : baseEnd_710743 < baseStart_710743 := by decide
  rcases family_descends (prefixWord ++ tailWord_710743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710774 : List Nat := [5, 1, 1, 2, 1, 3, 8]
def baseStart_710774 : Nat := 118140960795 + 710774 * 2 ^ 59
def prefixEnd_710774 : Nat := 4983230072969 + 3 ^ 40 * 710774 * 2
def baseEnd_710774 : Nat := 18023145615748509983023

theorem tailTrace_710774 : CollatzResearch.WordTrace tailWord_710774 prefixEnd_710774 18023145615748509983023 := by
  unfold tailWord_710774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620253595437166461244711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17282705017996442253276917 1620253595437166461244711)
  ·
    refine ⟨2430380393155749691867067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1620253595437166461244711 2430380393155749691867067)
    ·
      refine ⟨3645570589733624537800601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2430380393155749691867067 3645570589733624537800601)
      ·
        refine ⟨2734177942300218403350451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3645570589733624537800601 2734177942300218403350451)
        ·
          refine ⟨4101266913450327605025677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734177942300218403350451 4101266913450327605025677)
          ·
            refine ⟨1537975092543872851884629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4101266913450327605025677 1537975092543872851884629)
            ·
              refine ⟨18023145615748509983023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1537975092543872851884629 18023145615748509983023)
              ·
                rfl

theorem cell21_710774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 8].length) (baseStart_710774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710774 prefixEnd_710774 := by exact prefixLift 710774
  have htrace : WordTrace (prefixWord ++ tailWord_710774) baseStart_710774 baseEnd_710774 := by
    simpa [prefixWord, tailWord_710774, baseEnd_710774] using wordTrace_append hprefix tailTrace_710774
  have hstable : (prefixWord ++ tailWord_710774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710774).length < 2 ^ (prefixWord ++ tailWord_710774).sum := by decide
  have hdescent : baseEnd_710774 < baseStart_710774 := by decide
  rcases family_descends (prefixWord ++ tailWord_710774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710808 : List Nat := [2, 1, 2, 4, 4, 1, 2, 5]
def baseStart_710808 : Nat := 118140960795 + 710808 * 2 ^ 59
def prefixEnd_710808 : Nat := 4983230072969 + 3 ^ 40 * 710808 * 2
def baseEnd_710808 : Nat := 54072023268320028760157

theorem tailTrace_710808 : CollatzResearch.WordTrace tailWord_710808 prefixEnd_710808 54072023268320028760157 := by
  unfold tailWord_710808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12962648804435743593326539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17283531739247658124435385 12962648804435743593326539)
  ·
    refine ⟨19443973206653615389989809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12962648804435743593326539 19443973206653615389989809)
    ·
      refine ⟨14582979904990211542492357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19443973206653615389989809 14582979904990211542492357)
      ·
        refine ⟨2734308732185664664217317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14582979904990211542492357 2734308732185664664217317)
        ·
          refine ⟨512682887284812124540747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2734308732185664664217317 512682887284812124540747)
          ·
            refine ⟨769024330927218186811121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512682887284812124540747 769024330927218186811121)
            ·
              refine ⟨576768248195413640108341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769024330927218186811121 576768248195413640108341)
              ·
                refine ⟨54072023268320028760157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 576768248195413640108341 54072023268320028760157)
                ·
                  rfl

theorem cell21_710808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_710808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710808 prefixEnd_710808 := by exact prefixLift 710808
  have htrace : WordTrace (prefixWord ++ tailWord_710808) baseStart_710808 baseEnd_710808 := by
    simpa [prefixWord, tailWord_710808, baseEnd_710808] using wordTrace_append hprefix tailTrace_710808
  have hstable : (prefixWord ++ tailWord_710808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710808).length < 2 ^ (prefixWord ++ tailWord_710808).sum := by decide
  have hdescent : baseEnd_710808 < baseStart_710808 := by decide
  rcases family_descends (prefixWord ++ tailWord_710808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710881 : List Nat := [1, 2, 3, 1, 3, 1, 2, 5, 3]
def baseStart_710881 : Nat := 118140960795 + 710881 * 2 ^ 59
def prefixEnd_710881 : Nat := 4983230072969 + 3 ^ 40 * 710881 * 2
def baseEnd_710881 : Nat := 162232729399528181563655

theorem tailTrace_710881 : CollatzResearch.WordTrace tailWord_710881 prefixEnd_710881 162232729399528181563655 := by
  unfold tailWord_710881
  simp only [CollatzResearch.WordTrace]
  refine ⟨25927960137607020654060497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17285306758404680436040331 25927960137607020654060497)
  ·
    refine ⟨19445970103205265490545373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25927960137607020654060497 19445970103205265490545373)
    ·
      refine ⟨7292238788701974558954515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19445970103205265490545373 7292238788701974558954515)
      ·
        refine ⟨10938358183052961838431773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7292238788701974558954515 10938358183052961838431773)
        ·
          refine ⟨4101884318644860689411915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10938358183052961838431773 4101884318644860689411915)
          ·
            refine ⟨6152826477967291034117873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101884318644860689411915 6152826477967291034117873)
            ·
              refine ⟨4614619858475468275588405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6152826477967291034117873 4614619858475468275588405)
              ·
                refine ⟨432620611732075150836413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4614619858475468275588405 432620611732075150836413)
                ·
                  refine ⟨162232729399528181563655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432620611732075150836413 162232729399528181563655)
                  ·
                    rfl

theorem cell21_710881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_710881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710881 prefixEnd_710881 := by exact prefixLift 710881
  have htrace : WordTrace (prefixWord ++ tailWord_710881) baseStart_710881 baseEnd_710881 := by
    simpa [prefixWord, tailWord_710881, baseEnd_710881] using wordTrace_append hprefix tailTrace_710881
  have hstable : (prefixWord ++ tailWord_710881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710881).length < 2 ^ (prefixWord ++ tailWord_710881).sum := by decide
  have hdescent : baseEnd_710881 < baseStart_710881 := by decide
  rcases family_descends (prefixWord ++ tailWord_710881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710895 : List Nat := [1, 1, 2, 1, 6, 1, 1, 4, 4]
def baseStart_710895 : Nat := 118140960795 + 710895 * 2 ^ 59
def prefixEnd_710895 : Nat := 4983230072969 + 3 ^ 40 * 710895 * 2
def baseEnd_710895 : Nat := 162235924390267268330293

theorem tailTrace_710895 : CollatzResearch.WordTrace tailWord_710895 prefixEnd_710895 162235924390267268330293 := by
  unfold tailWord_710895
  simp only [CollatzResearch.WordTrace]
  refine ⟨25928470759556301045070139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17285647173037534030046759 25928470759556301045070139)
  ·
    refine ⟨38892706139334451567605209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25928470759556301045070139 38892706139334451567605209)
    ·
      refine ⟨29169529604500838675703907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38892706139334451567605209 29169529604500838675703907)
      ·
        refine ⟨43754294406751258013555861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29169529604500838675703907 43754294406751258013555861)
        ·
          refine ⟨2050982550316465219385431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43754294406751258013555861 2050982550316465219385431)
          ·
            refine ⟨3076473825474697829078147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050982550316465219385431 3076473825474697829078147)
            ·
              refine ⟨4614710738212046743617221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076473825474697829078147 4614710738212046743617221)
              ·
                refine ⟨865258263414758764428229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4614710738212046743617221 865258263414758764428229)
                ·
                  refine ⟨162235924390267268330293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865258263414758764428229 162235924390267268330293)
                  ·
                    rfl

theorem cell21_710895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 4].length) (baseStart_710895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710895 prefixEnd_710895 := by exact prefixLift 710895
  have htrace : WordTrace (prefixWord ++ tailWord_710895) baseStart_710895 baseEnd_710895 := by
    simpa [prefixWord, tailWord_710895, baseEnd_710895] using wordTrace_append hprefix tailTrace_710895
  have hstable : (prefixWord ++ tailWord_710895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710895).length < 2 ^ (prefixWord ++ tailWord_710895).sum := by decide
  have hdescent : baseEnd_710895 < baseStart_710895 := by decide
  rcases family_descends (prefixWord ++ tailWord_710895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710898 : List Nat := [3, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_710898 : Nat := 118140960795 + 710898 * 2 ^ 59
def prefixEnd_710898 : Nat := 4983230072969 + 3 ^ 40 * 710898 * 2
def baseEnd_710898 : Nat := 162236609031139929780287

theorem tailTrace_710898 : CollatzResearch.WordTrace tailWord_710898 prefixEnd_710898 162236609031139929780287 := by
  unfold tailWord_710898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6482145044636358139357337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17285720119030288371619565 6482145044636358139357337)
  ·
    refine ⟨4861608783477268604518003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6482145044636358139357337 4861608783477268604518003)
    ·
      refine ⟨7292413175215902906777005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4861608783477268604518003 7292413175215902906777005)
      ·
        refine ⟨2734654940705963590041377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7292413175215902906777005 2734654940705963590041377)
        ·
          refine ⟨2050991205529472692531033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2734654940705963590041377 2050991205529472692531033)
          ·
            refine ⟨1538243404147104519398275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2050991205529472692531033 1538243404147104519398275)
            ·
              refine ⟨2307365106220656779097413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538243404147104519398275 2307365106220656779097413)
              ·
                refine ⟨432630957416373146080765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2307365106220656779097413 432630957416373146080765)
                ·
                  refine ⟨162236609031139929780287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432630957416373146080765 162236609031139929780287)
                  ·
                    rfl

theorem cell21_710898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_710898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710898 prefixEnd_710898 := by exact prefixLift 710898
  have htrace : WordTrace (prefixWord ++ tailWord_710898) baseStart_710898 baseEnd_710898 := by
    simpa [prefixWord, tailWord_710898, baseEnd_710898] using wordTrace_append hprefix tailTrace_710898
  have hstable : (prefixWord ++ tailWord_710898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710898).length < 2 ^ (prefixWord ++ tailWord_710898).sum := by decide
  have hdescent : baseEnd_710898 < baseStart_710898 := by decide
  rcases family_descends (prefixWord ++ tailWord_710898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710926 : List Nat := [4, 1, 1, 2, 1, 2, 5, 5]
def baseStart_710926 : Nat := 118140960795 + 710926 * 2 ^ 59
def prefixEnd_710926 : Nat := 4983230072969 + 3 ^ 40 * 710926 * 2
def baseEnd_710926 : Nat := 54080999670872701104521

theorem tailTrace_710926 : CollatzResearch.WordTrace tailWord_710926 prefixEnd_710926 54080999670872701104521 := by
  unfold tailWord_710926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3241200177805499167431079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17286400948295995559632421 3241200177805499167431079)
  ·
    refine ⟨4861800266708248751146619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3241200177805499167431079 4861800266708248751146619)
    ·
      refine ⟨7292700400062373126719929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4861800266708248751146619 7292700400062373126719929)
      ·
        refine ⟨5469525300046779845039947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7292700400062373126719929 5469525300046779845039947)
        ·
          refine ⟨8204287950070169767559921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5469525300046779845039947 8204287950070169767559921)
          ·
            refine ⟨6153215962552627325669941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8204287950070169767559921 6153215962552627325669941)
            ·
              refine ⟨576863996489308811781557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6153215962552627325669941 576863996489308811781557)
              ·
                refine ⟨54080999670872701104521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 576863996489308811781557 54080999670872701104521)
                ·
                  rfl

theorem cell21_710926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_710926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_710926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_710926 prefixEnd_710926 := by exact prefixLift 710926
  have htrace : WordTrace (prefixWord ++ tailWord_710926) baseStart_710926 baseEnd_710926 := by
    simpa [prefixWord, tailWord_710926, baseEnd_710926] using wordTrace_append hprefix tailTrace_710926
  have hstable : (prefixWord ++ tailWord_710926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710926).length < 2 ^ (prefixWord ++ tailWord_710926).sum := by decide
  have hdescent : baseEnd_710926 < baseStart_710926 := by decide
  rcases family_descends (prefixWord ++ tailWord_710926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711064 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_711064 : Nat := 118140960795 + 711064 * 2 ^ 59
def prefixEnd_711064 : Nat := 4983230072969 + 3 ^ 40 * 711064 * 2
def baseEnd_711064 : Nat := 162274492492760530013281

theorem tailTrace_711064 : CollatzResearch.WordTrace tailWord_711064 prefixEnd_711064 162274492492760530013281 := by
  unfold tailWord_711064
  simp only [CollatzResearch.WordTrace]
  refine ⟨12967317347972021453986123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17289756463962695271981497 12967317347972021453986123)
  ·
    refine ⟨19450976021958032180979185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12967317347972021453986123 19450976021958032180979185)
    ·
      refine ⟨14588232016468524135734389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19450976021958032180979185 14588232016468524135734389)
      ·
        refine ⟨1367646751543924137725099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14588232016468524135734389 1367646751543924137725099)
        ·
          refine ⟨2051470127315886206587649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367646751543924137725099 2051470127315886206587649)
          ·
            refine ⟨1538602595486914654940737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2051470127315886206587649 1538602595486914654940737)
            ·
              refine ⟨1153951946615185991205553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538602595486914654940737 1153951946615185991205553)
              ·
                refine ⟨865463959961389493404165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153951946615185991205553 865463959961389493404165)
                ·
                  refine ⟨162274492492760530013281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865463959961389493404165 162274492492760530013281)
                  ·
                    rfl

theorem cell21_711064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_711064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711064 prefixEnd_711064 := by exact prefixLift 711064
  have htrace : WordTrace (prefixWord ++ tailWord_711064) baseStart_711064 baseEnd_711064 := by
    simpa [prefixWord, tailWord_711064, baseEnd_711064] using wordTrace_append hprefix tailTrace_711064
  have hstable : (prefixWord ++ tailWord_711064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711064).length < 2 ^ (prefixWord ++ tailWord_711064).sum := by decide
  have hdescent : baseEnd_711064 < baseStart_711064 := by decide
  rcases family_descends (prefixWord ++ tailWord_711064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711126 : List Nat := [5, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_711126 : Nat := 118140960795 + 711126 * 2 ^ 59
def prefixEnd_711126 : Nat := 4983230072969 + 3 ^ 40 * 711126 * 2
def baseEnd_711126 : Nat := 162288641737462199979821

theorem tailTrace_711126 : CollatzResearch.WordTrace tailWord_711126 prefixEnd_711126 162288641737462199979821 := by
  unfold tailWord_711126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621056001357464218545577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17291264014479618331152821 1621056001357464218545577)
  ·
    refine ⟨1215792001018098163909183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1621056001357464218545577 1215792001018098163909183)
    ·
      refine ⟨1823688001527147245863775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1215792001018098163909183 1823688001527147245863775)
      ·
        refine ⟨2735532002290720868795663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1823688001527147245863775 2735532002290720868795663)
        ·
          refine ⟨4103298003436081303193495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735532002290720868795663 4103298003436081303193495)
          ·
            refine ⟨6154947005154121954790243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103298003436081303193495 6154947005154121954790243)
            ·
              refine ⟨9232420507731182932185365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154947005154121954790243 9232420507731182932185365)
              ·
                refine ⟨432769711299899199946189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9232420507731182932185365 432769711299899199946189)
                ·
                  refine ⟨162288641737462199979821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432769711299899199946189 162288641737462199979821)
                  ·
                    rfl

theorem cell21_711126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_711126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711126 prefixEnd_711126 := by exact prefixLift 711126
  have htrace : WordTrace (prefixWord ++ tailWord_711126) baseStart_711126 baseEnd_711126 := by
    simpa [prefixWord, tailWord_711126, baseEnd_711126] using wordTrace_append hprefix tailTrace_711126
  have hstable : (prefixWord ++ tailWord_711126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711126).length < 2 ^ (prefixWord ++ tailWord_711126).sum := by decide
  have hdescent : baseEnd_711126 < baseStart_711126 := by decide
  rcases family_descends (prefixWord ++ tailWord_711126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711154 : List Nat := [3, 2, 1, 4, 2, 1, 1, 7]
def baseStart_711154 : Nat := 118140960795 + 711154 * 2 ^ 59
def prefixEnd_711154 : Nat := 4983230072969 + 3 ^ 40 * 711154 * 2
def baseEnd_711154 : Nat := 54098343906313457837699

theorem tailTrace_711154 : CollatzResearch.WordTrace tailWord_711154 prefixEnd_711154 54098343906313457837699 := by
  unfold tailWord_711154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484479316404497069687129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17291944843745325519165677 6484479316404497069687129)
  ·
    refine ⟨4863359487303372802265347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6484479316404497069687129 4863359487303372802265347)
    ·
      refine ⟨7295039230955059203398021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4863359487303372802265347 7295039230955059203398021)
      ·
        refine ⟨1367819855804073600637129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7295039230955059203398021 1367819855804073600637129)
        ·
          refine ⟨1025864891853055200477847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1367819855804073600637129 1025864891853055200477847)
          ·
            refine ⟨1538797337779582800716771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025864891853055200477847 1538797337779582800716771)
            ·
              refine ⟨2308196006669374201075157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538797337779582800716771 2308196006669374201075157)
              ·
                refine ⟨54098343906313457837699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2308196006669374201075157 54098343906313457837699)
                ·
                  rfl

theorem cell21_711154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_711154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711154 prefixEnd_711154 := by exact prefixLift 711154
  have htrace : WordTrace (prefixWord ++ tailWord_711154) baseStart_711154 baseEnd_711154 := by
    simpa [prefixWord, tailWord_711154, baseEnd_711154] using wordTrace_append hprefix tailTrace_711154
  have hstable : (prefixWord ++ tailWord_711154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711154).length < 2 ^ (prefixWord ++ tailWord_711154).sum := by decide
  have hdescent : baseEnd_711154 < baseStart_711154 := by decide
  rcases family_descends (prefixWord ++ tailWord_711154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711230 : List Nat := [4, 2, 1, 4, 1, 9]
def baseStart_711230 : Nat := 118140960795 + 711230 * 2 ^ 59
def prefixEnd_711230 : Nat := 4983230072969 + 3 ^ 40 * 711230 * 2
def baseEnd_711230 : Nat := 6011569479791893712825

theorem tailTrace_711230 : CollatzResearch.WordTrace tailWord_711230 prefixEnd_711230 6011569479791893712825 := by
  unfold tailWord_711230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242586151667831657314393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17293792808895102172343429 3242586151667831657314393)
  ·
    refine ⟨2431939613750873742985795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3242586151667831657314393 2431939613750873742985795)
    ·
      refine ⟨3647909420626310614478693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2431939613750873742985795 3647909420626310614478693)
      ·
        refine ⟨683983016367433240214755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3647909420626310614478693 683983016367433240214755)
        ·
          refine ⟨1025974524551149860322133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683983016367433240214755 1025974524551149860322133)
          ·
            refine ⟨6011569479791893712825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1025974524551149860322133 6011569479791893712825)
            ·
              rfl

theorem cell21_711230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 9].length) (baseStart_711230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711230 prefixEnd_711230 := by exact prefixLift 711230
  have htrace : WordTrace (prefixWord ++ tailWord_711230) baseStart_711230 baseEnd_711230 := by
    simpa [prefixWord, tailWord_711230, baseEnd_711230] using wordTrace_append hprefix tailTrace_711230
  have hstable : (prefixWord ++ tailWord_711230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711230).length < 2 ^ (prefixWord ++ tailWord_711230).sum := by decide
  have hdescent : baseEnd_711230 < baseStart_711230 := by decide
  rcases family_descends (prefixWord ++ tailWord_711230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711236 : List Nat := [2, 3, 5, 1, 1, 1, 1, 4, 3]
def baseStart_711236 : Nat := 118140960795 + 711236 * 2 ^ 59
def prefixEnd_711236 : Nat := 4983230072969 + 3 ^ 40 * 711236 * 2
def baseEnd_711236 : Nat := 162313745236126453146263

theorem tailTrace_711236 : CollatzResearch.WordTrace tailWord_711236 prefixEnd_711236 162313745236126453146263 := by
  unfold tailWord_711236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12970454025660458141616781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17293938700880610855489041 12970454025660458141616781)
  ·
    refine ⟨4863920259622671803106293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12970454025660458141616781 4863920259622671803106293)
    ·
      refine ⟨455992524339625481541215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4863920259622671803106293 455992524339625481541215)
      ·
        refine ⟨683988786509438222311823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455992524339625481541215 683988786509438222311823)
        ·
          refine ⟨1025983179764157333467735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683988786509438222311823 1025983179764157333467735)
          ·
            refine ⟨1538974769646236000201603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025983179764157333467735 1538974769646236000201603)
            ·
              refine ⟨2308462154469354000302405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538974769646236000201603 2308462154469354000302405)
              ·
                refine ⟨432836653963003875056701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2308462154469354000302405 432836653963003875056701)
                ·
                  refine ⟨162313745236126453146263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432836653963003875056701 162313745236126453146263)
                  ·
                    rfl

theorem cell21_711236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_711236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711236 prefixEnd_711236 := by exact prefixLift 711236
  have htrace : WordTrace (prefixWord ++ tailWord_711236) baseStart_711236 baseEnd_711236 := by
    simpa [prefixWord, tailWord_711236, baseEnd_711236] using wordTrace_append hprefix tailTrace_711236
  have hstable : (prefixWord ++ tailWord_711236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711236).length < 2 ^ (prefixWord ++ tailWord_711236).sum := by decide
  have hdescent : baseEnd_711236 < baseStart_711236 := by decide
  rcases family_descends (prefixWord ++ tailWord_711236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711278 : List Nat := [4, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_711278 : Nat := 118140960795 + 711278 * 2 ^ 59
def prefixEnd_711278 : Nat := 4983230072969 + 3 ^ 40 * 711278 * 2
def baseEnd_711278 : Nat := 162323330208343713446177

theorem tailTrace_711278 : CollatzResearch.WordTrace tailWord_711278 prefixEnd_711278 162323330208343713446177 := by
  unfold tailWord_711278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242804989646094682032811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17294959944779171637508325 3242804989646094682032811)
  ·
    refine ⟨4864207484469142023049217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3242804989646094682032811 4864207484469142023049217)
    ·
      refine ⟨3648155613351856517286913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4864207484469142023049217 3648155613351856517286913)
      ·
        refine ⟨2736116710013892387965185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3648155613351856517286913 2736116710013892387965185)
        ·
          refine ⟨2052087532510419290973889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2736116710013892387965185 2052087532510419290973889)
          ·
            refine ⟨1539065649382814468230417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052087532510419290973889 1539065649382814468230417)
            ·
              refine ⟨1154299237037110851172813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539065649382814468230417 1154299237037110851172813)
              ·
                refine ⟨432862213888916569189805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1154299237037110851172813 432862213888916569189805)
                ·
                  refine ⟨162323330208343713446177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432862213888916569189805 162323330208343713446177)
                  ·
                    rfl

theorem cell21_711278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_711278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711278 prefixEnd_711278 := by exact prefixLift 711278
  have htrace : WordTrace (prefixWord ++ tailWord_711278) baseStart_711278 baseEnd_711278 := by
    simpa [prefixWord, tailWord_711278, baseEnd_711278] using wordTrace_append hprefix tailTrace_711278
  have hstable : (prefixWord ++ tailWord_711278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711278).length < 2 ^ (prefixWord ++ tailWord_711278).sum := by decide
  have hdescent : baseEnd_711278 < baseStart_711278 := by decide
  rcases family_descends (prefixWord ++ tailWord_711278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711368 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_711368 : Nat := 118140960795 + 711368 * 2 ^ 59
def prefixEnd_711368 : Nat := 4983230072969 + 3 ^ 40 * 711368 * 2
def baseEnd_711368 : Nat := 162343869434523556945993

theorem tailTrace_711368 : CollatzResearch.WordTrace tailWord_711368 prefixEnd_711368 162343869434523556945993 := by
  unfold tailWord_711368
  simp only [CollatzResearch.WordTrace]
  refine ⟨12972861243421351413519379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17297148324561801884692505 12972861243421351413519379)
  ·
    refine ⟨19459291865132027120279069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12972861243421351413519379 19459291865132027120279069)
    ·
      refine ⟨7297234449424510170104651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19459291865132027120279069 7297234449424510170104651)
      ·
        refine ⟨10945851674136765255156977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297234449424510170104651 10945851674136765255156977)
        ·
          refine ⟨8209388755602573941367733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10945851674136765255156977 8209388755602573941367733)
          ·
            refine ⟨769630195837741307003225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8209388755602573941367733 769630195837741307003225)
            ·
              refine ⟨577222646878305980252419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769630195837741307003225 577222646878305980252419)
              ·
                refine ⟨865833970317458970378629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577222646878305980252419 865833970317458970378629)
                ·
                  refine ⟨162343869434523556945993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 865833970317458970378629 162343869434523556945993)
                  ·
                    rfl

theorem cell21_711368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_711368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711368 prefixEnd_711368 := by exact prefixLift 711368
  have htrace : WordTrace (prefixWord ++ tailWord_711368) baseStart_711368 baseEnd_711368 := by
    simpa [prefixWord, tailWord_711368, baseEnd_711368] using wordTrace_append hprefix tailTrace_711368
  have hstable : (prefixWord ++ tailWord_711368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711368).length < 2 ^ (prefixWord ++ tailWord_711368).sum := by decide
  have hdescent : baseEnd_711368 < baseStart_711368 := by decide
  rcases family_descends (prefixWord ++ tailWord_711368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711492 : List Nat := [2, 3, 4, 2, 1, 2, 2, 5]
def baseStart_711492 : Nat := 118140960795 + 711492 * 2 ^ 59
def prefixEnd_711492 : Nat := 4983230072969 + 3 ^ 40 * 711492 * 2
def baseEnd_711492 : Nat := 54124055974642298959691

theorem tailTrace_711492 : CollatzResearch.WordTrace tailWord_711492 prefixEnd_711492 54124055974642298959691 := by
  unfold tailWord_711492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975122569196736002276365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17300163425595648003035153 12975122569196736002276365)
  ·
    refine ⟨4865670963448776000853637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12975122569196736002276365 4865670963448776000853637)
    ·
      refine ⟨912313305646645500160057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4865670963448776000853637 912313305646645500160057)
      ·
        refine ⟨684234979234984125120043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912313305646645500160057 684234979234984125120043)
        ·
          refine ⟨1026352468852476187680065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684234979234984125120043 1026352468852476187680065)
          ·
            refine ⟨769764351639357140760049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1026352468852476187680065 769764351639357140760049)
            ·
              refine ⟨577323263729517855570037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769764351639357140760049 577323263729517855570037)
              ·
                refine ⟨54124055974642298959691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 577323263729517855570037 54124055974642298959691)
                ·
                  rfl

theorem cell21_711492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_711492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711492 prefixEnd_711492 := by exact prefixLift 711492
  have htrace : WordTrace (prefixWord ++ tailWord_711492) baseStart_711492 baseEnd_711492 := by
    simpa [prefixWord, tailWord_711492, baseEnd_711492] using wordTrace_append hprefix tailTrace_711492
  have hstable : (prefixWord ++ tailWord_711492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711492).length < 2 ^ (prefixWord ++ tailWord_711492).sum := by decide
  have hdescent : baseEnd_711492 < baseStart_711492 := by decide
  rcases family_descends (prefixWord ++ tailWord_711492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711531 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 5]
def baseStart_711531 : Nat := 118140960795 + 711531 * 2 ^ 59
def prefixEnd_711531 : Nat := 4983230072969 + 3 ^ 40 * 711531 * 2
def baseEnd_711531 : Nat := 162381068255271495728993

theorem tailTrace_711531 : CollatzResearch.WordTrace tailWord_711531 prefixEnd_711531 162381068255271495728993 := by
  unfold tailWord_711531
  simp only [CollatzResearch.WordTrace]
  refine ⟨25951667585252181665222447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17301111723501454443481631 25951667585252181665222447)
  ·
    refine ⟨38927501377878272497833671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25951667585252181665222447 38927501377878272497833671)
    ·
      refine ⟨58391252066817408746750507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38927501377878272497833671 58391252066817408746750507)
      ·
        refine ⟨87586878100226113120125761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58391252066817408746750507 87586878100226113120125761)
        ·
          refine ⟨65690158575169584840094321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87586878100226113120125761 65690158575169584840094321)
          ·
            refine ⟨49267618931377188630070741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65690158575169584840094321 49267618931377188630070741)
            ·
              refine ⟨1154709818704152858517283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49267618931377188630070741 1154709818704152858517283)
              ·
                refine ⟨1732064728056229287775925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154709818704152858517283 1732064728056229287775925)
                ·
                  refine ⟨162381068255271495728993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1732064728056229287775925 162381068255271495728993)
                  ·
                    rfl

theorem cell21_711531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_711531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711531 prefixEnd_711531 := by exact prefixLift 711531
  have htrace : WordTrace (prefixWord ++ tailWord_711531) baseStart_711531 baseEnd_711531 := by
    simpa [prefixWord, tailWord_711531, baseEnd_711531] using wordTrace_append hprefix tailTrace_711531
  have hstable : (prefixWord ++ tailWord_711531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711531).length < 2 ^ (prefixWord ++ tailWord_711531).sum := by decide
  have hdescent : baseEnd_711531 < baseStart_711531 := by decide
  rcases family_descends (prefixWord ++ tailWord_711531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711534 : List Nat := [4, 1, 2, 3, 2, 1, 2, 6]
def baseStart_711534 : Nat := 118140960795 + 711534 * 2 ^ 59
def prefixEnd_711534 : Nat := 4983230072969 + 3 ^ 40 * 711534 * 2
def baseEnd_711534 : Nat := 54127250965381385726329

theorem tailTrace_711534 : CollatzResearch.WordTrace tailWord_711534 prefixEnd_711534 54127250965381385726329 := by
  unfold tailWord_711534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243972125530164147197707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17301184669494208785054437 3243972125530164147197707)
  ·
    refine ⟨4865958188295246220796561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3243972125530164147197707 4865958188295246220796561)
    ·
      refine ⟨3649468641221434665597421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4865958188295246220796561 3649468641221434665597421)
      ·
        refine ⟨1368550740458037999599033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3649468641221434665597421 1368550740458037999599033)
        ·
          refine ⟨1026413055343528499699275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1368550740458037999599033 1026413055343528499699275)
          ·
            refine ⟨1539619583015292749548913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026413055343528499699275 1539619583015292749548913)
            ·
              refine ⟨1154714687261469562161685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539619583015292749548913 1154714687261469562161685)
              ·
                refine ⟨54127250965381385726329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1154714687261469562161685 54127250965381385726329)
                ·
                  rfl

theorem cell21_711534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_711534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711534 prefixEnd_711534 := by exact prefixLift 711534
  have htrace : WordTrace (prefixWord ++ tailWord_711534) baseStart_711534 baseEnd_711534 := by
    simpa [prefixWord, tailWord_711534, baseEnd_711534] using wordTrace_append hprefix tailTrace_711534
  have hstable : (prefixWord ++ tailWord_711534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711534).length < 2 ^ (prefixWord ++ tailWord_711534).sum := by decide
  have hdescent : baseEnd_711534 < baseStart_711534 := by decide
  rcases family_descends (prefixWord ++ tailWord_711534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711745 : List Nat := [1, 2, 5, 1, 4, 8]
def baseStart_711745 : Nat := 118140960795 + 711745 * 2 ^ 59
def prefixEnd_711745 : Nat := 4983230072969 + 3 ^ 40 * 711745 * 2
def baseEnd_711745 : Nat := 6015922443364988117107

theorem tailTrace_711745 : CollatzResearch.WordTrace tailWord_711745 prefixEnd_711745 6015922443364988117107 := by
  unfold tailWord_711745
  simp only [CollatzResearch.WordTrace]
  refine ⟨25959472806476896213512689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17306315204317930809008459 25959472806476896213512689)
  ·
    refine ⟨19469604604857672160134517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25959472806476896213512689 19469604604857672160134517)
    ·
      refine ⟨1825275431705406765012611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19469604604857672160134517 1825275431705406765012611)
      ·
        refine ⟨2737913147558110147518917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825275431705406765012611 2737913147558110147518917)
        ·
          refine ⟨513358715167145652659797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2737913147558110147518917 513358715167145652659797)
          ·
            refine ⟨6015922443364988117107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 513358715167145652659797 6015922443364988117107)
            ·
              rfl

theorem cell21_711745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 8].length) (baseStart_711745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711745 prefixEnd_711745 := by exact prefixLift 711745
  have htrace : WordTrace (prefixWord ++ tailWord_711745) baseStart_711745 baseEnd_711745 := by
    simpa [prefixWord, tailWord_711745, baseEnd_711745] using wordTrace_append hprefix tailTrace_711745
  have hstable : (prefixWord ++ tailWord_711745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711745).length < 2 ^ (prefixWord ++ tailWord_711745).sum := by decide
  have hdescent : baseEnd_711745 < baseStart_711745 := by decide
  rcases family_descends (prefixWord ++ tailWord_711745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711838 : List Nat := [4, 3, 1, 1, 2, 1, 4, 5]
def baseStart_711838 : Nat := 118140960795 + 711838 * 2 ^ 59
def prefixEnd_711838 : Nat := 4983230072969 + 3 ^ 40 * 711838 * 2
def baseEnd_711838 : Nat := 54150376612635728037233

theorem tailTrace_711838 : CollatzResearch.WordTrace tailWord_711838 prefixEnd_711838 54150376612635728037233 := by
  unfold tailWord_711838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245358099392496637081021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17308576530093315397765445 3245358099392496637081021)
  ·
    refine ⟨1217009287272186238905383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3245358099392496637081021 1217009287272186238905383)
    ·
      refine ⟨1825513930908279358358075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1217009287272186238905383 1825513930908279358358075)
      ·
        refine ⟨2738270896362419037537113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1825513930908279358358075 2738270896362419037537113)
        ·
          refine ⟨2053703172271814278152835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2738270896362419037537113 2053703172271814278152835)
          ·
            refine ⟨3080554758407721417229253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053703172271814278152835 3080554758407721417229253)
            ·
              refine ⟨577604017201447765730485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3080554758407721417229253 577604017201447765730485)
              ·
                refine ⟨54150376612635728037233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 577604017201447765730485 54150376612635728037233)
                ·
                  rfl

theorem cell21_711838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_711838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711838 prefixEnd_711838 := by exact prefixLift 711838
  have htrace : WordTrace (prefixWord ++ tailWord_711838) baseStart_711838 baseEnd_711838 := by
    simpa [prefixWord, tailWord_711838, baseEnd_711838] using wordTrace_append hprefix tailTrace_711838
  have hstable : (prefixWord ++ tailWord_711838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711838).length < 2 ^ (prefixWord ++ tailWord_711838).sum := by decide
  have hdescent : baseEnd_711838 < baseStart_711838 := by decide
  rcases family_descends (prefixWord ++ tailWord_711838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711987 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 5]
def baseStart_711987 : Nat := 118140960795 + 711987 * 2 ^ 59
def prefixEnd_711987 : Nat := 4983230072969 + 3 ^ 40 * 711987 * 2
def baseEnd_711987 : Nat := 162485133667916036128061

theorem tailTrace_711987 : CollatzResearch.WordTrace tailWord_711987 prefixEnd_711987 162485133667916036128061 := by
  unfold tailWord_711987
  simp only [CollatzResearch.WordTrace]
  refine ⟨25968299271600171543822215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17312199514400114362548143 25968299271600171543822215)
  ·
    refine ⟨38952448907400257315733323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25968299271600171543822215 38952448907400257315733323)
    ·
      refine ⟨58428673361100385973599985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38952448907400257315733323 58428673361100385973599985)
      ·
        refine ⟨43821505020825289480199989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58428673361100385973599985 43821505020825289480199989)
        ·
          refine ⟨4108266095702370888768749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43821505020825289480199989 4108266095702370888768749)
          ·
            refine ⟨1540599785888389083288281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4108266095702370888768749 1540599785888389083288281)
            ·
              refine ⟨1155449839416291812466211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540599785888389083288281 1155449839416291812466211)
              ·
                refine ⟨1733174759124437718699317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155449839416291812466211 1733174759124437718699317)
                ·
                  refine ⟨162485133667916036128061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1733174759124437718699317 162485133667916036128061)
                  ·
                    rfl

theorem cell21_711987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_711987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_711987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_711987 prefixEnd_711987 := by exact prefixLift 711987
  have htrace : WordTrace (prefixWord ++ tailWord_711987) baseStart_711987 baseEnd_711987 := by
    simpa [prefixWord, tailWord_711987, baseEnd_711987] using wordTrace_append hprefix tailTrace_711987
  have hstable : (prefixWord ++ tailWord_711987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711987).length < 2 ^ (prefixWord ++ tailWord_711987).sum := by decide
  have hdescent : baseEnd_711987 < baseStart_711987 := by decide
  rcases family_descends (prefixWord ++ tailWord_711987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712004 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_712004 : Nat := 118140960795 + 712004 * 2 ^ 59
def prefixEnd_712004 : Nat := 4983230072969 + 3 ^ 40 * 712004 * 2
def baseEnd_712004 : Nat := 162489013299527784344693

theorem tailTrace_712004 : CollatzResearch.WordTrace tailWord_712004 prefixEnd_712004 162489013299527784344693 := by
  unfold tailWord_712004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12984459656269291723595533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17312612875025722298127377 12984459656269291723595533)
  ·
    refine ⟨4869172371100984396348325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12984459656269291723595533 4869172371100984396348325)
    ·
      refine ⟨912969819581434574315311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4869172371100984396348325 912969819581434574315311)
      ·
        refine ⟨1369454729372151861472967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912969819581434574315311 1369454729372151861472967)
        ·
          refine ⟨2054182094058227792209451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369454729372151861472967 2054182094058227792209451)
          ·
            refine ⟨3081273141087341688314177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054182094058227792209451 3081273141087341688314177)
            ·
              refine ⟨2310954855815506266235633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081273141087341688314177 2310954855815506266235633)
              ·
                refine ⟨1733216141861629699676725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2310954855815506266235633 1733216141861629699676725)
                ·
                  refine ⟨162489013299527784344693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1733216141861629699676725 162489013299527784344693)
                  ·
                    rfl

theorem cell21_712004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_712004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712004 prefixEnd_712004 := by exact prefixLift 712004
  have htrace : WordTrace (prefixWord ++ tailWord_712004) baseStart_712004 baseEnd_712004 := by
    simpa [prefixWord, tailWord_712004, baseEnd_712004] using wordTrace_append hprefix tailTrace_712004
  have hstable : (prefixWord ++ tailWord_712004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712004).length < 2 ^ (prefixWord ++ tailWord_712004).sum := by decide
  have hdescent : baseEnd_712004 < baseStart_712004 := by decide
  rcases family_descends (prefixWord ++ tailWord_712004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712021 : List Nat := [1, 3, 2, 2, 3, 3, 1, 3, 3]
def baseStart_712021 : Nat := 118140960795 + 712021 * 2 ^ 59
def prefixEnd_712021 : Nat := 4983230072969 + 3 ^ 40 * 712021 * 2
def baseEnd_712021 : Nat := 162492892931139532561325

theorem tailTrace_712021 : CollatzResearch.WordTrace tailWord_712021 prefixEnd_712021 162492892931139532561325 := by
  unfold tailWord_712021
  simp only [CollatzResearch.WordTrace]
  refine ⟨25969539353476995350559917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17313026235651330233706611 25969539353476995350559917)
  ·
    refine ⟨9738577257553873256459969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25969539353476995350559917 9738577257553873256459969)
    ·
      refine ⟨7303932943165404942344977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9738577257553873256459969 7303932943165404942344977)
      ·
        refine ⟨5477949707374053706758733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7303932943165404942344977 5477949707374053706758733)
        ·
          refine ⟨2054231140265270140034525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5477949707374053706758733 2054231140265270140034525)
          ·
            refine ⟨770336677599476302512947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2054231140265270140034525 770336677599476302512947)
            ·
              refine ⟨1155505016399214453769421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770336677599476302512947 1155505016399214453769421)
              ·
                refine ⟨433314381149705420163533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1155505016399214453769421 433314381149705420163533)
                ·
                  refine ⟨162492892931139532561325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433314381149705420163533 162492892931139532561325)
                  ·
                    rfl

theorem cell21_712021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_712021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712021 prefixEnd_712021 := by exact prefixLift 712021
  have htrace : WordTrace (prefixWord ++ tailWord_712021) baseStart_712021 baseEnd_712021 := by
    simpa [prefixWord, tailWord_712021, baseEnd_712021] using wordTrace_append hprefix tailTrace_712021
  have hstable : (prefixWord ++ tailWord_712021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712021).length < 2 ^ (prefixWord ++ tailWord_712021).sum := by decide
  have hdescent : baseEnd_712021 < baseStart_712021 := by decide
  rcases family_descends (prefixWord ++ tailWord_712021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712032 : List Nat := [2, 1, 1, 3, 4, 3, 7]
def baseStart_712032 : Nat := 118140960795 + 712032 * 2 ^ 59
def prefixEnd_712032 : Nat := 4983230072969 + 3 ^ 40 * 712032 * 2
def baseEnd_712032 : Nat := 18055044809000661986441

theorem tailTrace_712032 : CollatzResearch.WordTrace tailWord_712032 prefixEnd_712032 18055044809000661986441 := by
  unfold tailWord_712032
  simp only [CollatzResearch.WordTrace]
  refine ⟨12984970278218572114605175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17313293704291429486140233 12984970278218572114605175)
  ·
    refine ⟨19477455417327858171907763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12984970278218572114605175 19477455417327858171907763)
    ·
      refine ⟨29216183125991787257861645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19477455417327858171907763 29216183125991787257861645)
      ·
        refine ⟨10956068672246920221698117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29216183125991787257861645 10956068672246920221698117)
        ·
          refine ⟨2054262876046297541568397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10956068672246920221698117 2054262876046297541568397)
          ·
            refine ⟨770348578517361578088149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2054262876046297541568397 770348578517361578088149)
            ·
              refine ⟨18055044809000661986441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 770348578517361578088149 18055044809000661986441)
              ·
                rfl

theorem cell21_712032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 7].length) (baseStart_712032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712032 prefixEnd_712032 := by exact prefixLift 712032
  have htrace : WordTrace (prefixWord ++ tailWord_712032) baseStart_712032 baseEnd_712032 := by
    simpa [prefixWord, tailWord_712032, baseEnd_712032] using wordTrace_append hprefix tailTrace_712032
  have hstable : (prefixWord ++ tailWord_712032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712032).length < 2 ^ (prefixWord ++ tailWord_712032).sum := by decide
  have hdescent : baseEnd_712032 < baseStart_712032 := by decide
  rcases family_descends (prefixWord ++ tailWord_712032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712139 : List Nat := [1, 1, 1, 1, 3, 3, 3, 5, 3]
def baseStart_712139 : Nat := 118140960795 + 712139 * 2 ^ 59
def prefixEnd_712139 : Nat := 4983230072969 + 3 ^ 40 * 712139 * 2
def baseEnd_712139 : Nat := 162519822138797549594417

theorem tailTrace_712139 : CollatzResearch.WordTrace tailWord_712139 prefixEnd_712139 162519822138797549594417 := by
  unfold tailWord_712139
  simp only [CollatzResearch.WordTrace]
  refine ⟨25973843167049501503355471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17315895444699667668903647 25973843167049501503355471)
  ·
    refine ⟨38960764750574252255033207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25973843167049501503355471 38960764750574252255033207)
    ·
      refine ⟨58441147125861378382549811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38960764750574252255033207 58441147125861378382549811)
      ·
        refine ⟨87661720688792067573824717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58441147125861378382549811 87661720688792067573824717)
        ·
          refine ⟨32873145258297025340184269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87661720688792067573824717 32873145258297025340184269)
          ·
            refine ⟨12327429471861384502569101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32873145258297025340184269 12327429471861384502569101)
            ·
              refine ⟨4622786051948019188463413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12327429471861384502569101 4622786051948019188463413)
              ·
                refine ⟨433386192370126798918445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4622786051948019188463413 433386192370126798918445)
                ·
                  refine ⟨162519822138797549594417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433386192370126798918445 162519822138797549594417)
                  ·
                    rfl

theorem cell21_712139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 3].length) (baseStart_712139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712139 prefixEnd_712139 := by exact prefixLift 712139
  have htrace : WordTrace (prefixWord ++ tailWord_712139) baseStart_712139 baseEnd_712139 := by
    simpa [prefixWord, tailWord_712139, baseEnd_712139] using wordTrace_append hprefix tailTrace_712139
  have hstable : (prefixWord ++ tailWord_712139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712139).length < 2 ^ (prefixWord ++ tailWord_712139).sum := by decide
  have hdescent : baseEnd_712139 < baseStart_712139 := by decide
  rcases family_descends (prefixWord ++ tailWord_712139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712153 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 6]
def baseStart_712153 : Nat := 118140960795 + 712153 * 2 ^ 59
def prefixEnd_712153 : Nat := 4983230072969 + 3 ^ 40 * 712153 * 2
def baseEnd_712153 : Nat := 162523017129536636361055

theorem tailTrace_712153 : CollatzResearch.WordTrace tailWord_712153 prefixEnd_712153 162523017129536636361055 := by
  unfold tailWord_712153
  simp only [CollatzResearch.WordTrace]
  refine ⟨25974353788998781894365113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17316235859332521262910075 25974353788998781894365113)
  ·
    refine ⟨19480765341749086420773835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25974353788998781894365113 19480765341749086420773835)
    ·
      refine ⟨29221148012623629631160753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19480765341749086420773835 29221148012623629631160753)
      ·
        refine ⟨21915861009467722223370565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29221148012623629631160753 21915861009467722223370565)
        ·
          refine ⟨4109223939275197916881981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21915861009467722223370565 4109223939275197916881981)
          ·
            refine ⟨1540958977228199218830743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4109223939275197916881981 1540958977228199218830743)
            ·
              refine ⟨2311438465842298828246115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540958977228199218830743 2311438465842298828246115)
              ·
                refine ⟨3467157698763448242369173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311438465842298828246115 3467157698763448242369173)
                ·
                  refine ⟨162523017129536636361055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3467157698763448242369173 162523017129536636361055)
                  ·
                    rfl

theorem cell21_712153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_712153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712153 prefixEnd_712153 := by exact prefixLift 712153
  have htrace : WordTrace (prefixWord ++ tailWord_712153) baseStart_712153 baseEnd_712153 := by
    simpa [prefixWord, tailWord_712153, baseEnd_712153] using wordTrace_append hprefix tailTrace_712153
  have hstable : (prefixWord ++ tailWord_712153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712153).length < 2 ^ (prefixWord ++ tailWord_712153).sum := by decide
  have hdescent : baseEnd_712153 < baseStart_712153 := by decide
  rcases family_descends (prefixWord ++ tailWord_712153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712184 : List Nat := [2, 1, 2, 1, 1, 5, 4, 5]
def baseStart_712184 : Nat := 118140960795 + 712184 * 2 ^ 59
def prefixEnd_712184 : Nat := 4983230072969 + 3 ^ 40 * 712184 * 2
def baseEnd_712184 : Nat := 54176697250629157114775

theorem tailTrace_712184 : CollatzResearch.WordTrace tailWord_712184 prefixEnd_712184 54176697250629157114775 := by
  unfold tailWord_712184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987742225943237094371803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17316989634590982792495737 12987742225943237094371803)
  ·
    refine ⟨19481613338914855641557705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12987742225943237094371803 19481613338914855641557705)
    ·
      refine ⟨14611210004186141731168279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19481613338914855641557705 14611210004186141731168279)
      ·
        refine ⟨21916815006279212596752419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14611210004186141731168279 21916815006279212596752419)
        ·
          refine ⟨32875222509418818895128629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21916815006279212596752419 32875222509418818895128629)
          ·
            refine ⟨3082052110258014271418309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32875222509418818895128629 3082052110258014271418309)
            ·
              refine ⟨577884770673377675890933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3082052110258014271418309 577884770673377675890933)
              ·
                refine ⟨54176697250629157114775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 577884770673377675890933 54176697250629157114775)
                ·
                  rfl

theorem cell21_712184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_712184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712184 prefixEnd_712184 := by exact prefixLift 712184
  have htrace : WordTrace (prefixWord ++ tailWord_712184) baseStart_712184 baseEnd_712184 := by
    simpa [prefixWord, tailWord_712184, baseEnd_712184] using wordTrace_append hprefix tailTrace_712184
  have hstable : (prefixWord ++ tailWord_712184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712184).length < 2 ^ (prefixWord ++ tailWord_712184).sum := by decide
  have hdescent : baseEnd_712184 < baseStart_712184 := by decide
  rcases family_descends (prefixWord ++ tailWord_712184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712243 : List Nat := [1, 1, 1, 2, 4, 3, 2, 7]
def baseStart_712243 : Nat := 118140960795 + 712243 * 2 ^ 59
def prefixEnd_712243 : Nat := 4983230072969 + 3 ^ 40 * 712243 * 2
def baseEnd_712243 : Nat := 54181185451905493286957

theorem tailTrace_712243 : CollatzResearch.WordTrace tailWord_712243 prefixEnd_712243 54181185451905493286957 := by
  unfold tailWord_712243
  simp only [CollatzResearch.WordTrace]
  refine ⟨25977636358672727265141383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17318424239115151510094255 25977636358672727265141383)
  ·
    refine ⟨38966454538009090897712075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25977636358672727265141383 38966454538009090897712075)
    ·
      refine ⟨58449681807013636346568113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38966454538009090897712075 58449681807013636346568113)
      ·
        refine ⟨43837261355260227259926085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58449681807013636346568113 43837261355260227259926085)
        ·
          refine ⟨8219486504111292611236141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43837261355260227259926085 8219486504111292611236141)
          ·
            refine ⟨3082307439041734729213553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8219486504111292611236141 3082307439041734729213553)
            ·
              refine ⟨2311730579281301046910165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3082307439041734729213553 2311730579281301046910165)
              ·
                refine ⟨54181185451905493286957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2311730579281301046910165 54181185451905493286957)
                ·
                  rfl

theorem cell21_712243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 7].length) (baseStart_712243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712243 prefixEnd_712243 := by exact prefixLift 712243
  have htrace : WordTrace (prefixWord ++ tailWord_712243) baseStart_712243 baseEnd_712243 := by
    simpa [prefixWord, tailWord_712243, baseEnd_712243] using wordTrace_append hprefix tailTrace_712243
  have hstable : (prefixWord ++ tailWord_712243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712243).length < 2 ^ (prefixWord ++ tailWord_712243).sum := by decide
  have hdescent : baseEnd_712243 < baseStart_712243 := by decide
  rcases family_descends (prefixWord ++ tailWord_712243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712260 : List Nat := [2, 3, 5, 11]
def baseStart_712260 : Nat := 118140960795 + 712260 * 2 ^ 59
def prefixEnd_712260 : Nat := 4983230072969 + 3 ^ 40 * 712260 * 2
def baseEnd_712260 : Nat := 668919489659786946821

theorem tailTrace_712260 : CollatzResearch.WordTrace tailWord_712260 prefixEnd_712260 668919489659786946821 := by
  unfold tailWord_712260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989128199805569584255117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17318837599740759445673489 12989128199805569584255117)
  ·
    refine ⟨4870923074927088594095669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12989128199805569584255117 4870923074927088594095669)
    ·
      refine ⟨456649038274414555696469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4870923074927088594095669 456649038274414555696469)
      ·
        refine ⟨668919489659786946821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 456649038274414555696469 668919489659786946821)
        ·
          rfl

theorem cell21_712260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 11].length) (baseStart_712260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712260 prefixEnd_712260 := by exact prefixLift 712260
  have htrace : WordTrace (prefixWord ++ tailWord_712260) baseStart_712260 baseEnd_712260 := by
    simpa [prefixWord, tailWord_712260, baseEnd_712260] using wordTrace_append hprefix tailTrace_712260
  have hstable : (prefixWord ++ tailWord_712260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712260).length < 2 ^ (prefixWord ++ tailWord_712260).sum := by decide
  have hdescent : baseEnd_712260 < baseStart_712260 := by decide
  rcases family_descends (prefixWord ++ tailWord_712260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712288 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_712288 : Nat := 118140960795 + 712288 * 2 ^ 59
def prefixEnd_712288 : Nat := 4983230072969 + 3 ^ 40 * 712288 * 2
def baseEnd_712288 : Nat := 162553825968806401610779

theorem tailTrace_712288 : CollatzResearch.WordTrace tailWord_712288 prefixEnd_712288 162553825968806401610779 := by
  unfold tailWord_712288
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989638821754849975264759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17319518429006466633686345 12989638821754849975264759)
  ·
    refine ⟨19484458232632274962897139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12989638821754849975264759 19484458232632274962897139)
    ·
      refine ⟨29226687348948412444345709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19484458232632274962897139 29226687348948412444345709)
      ·
        refine ⟨10960007755855654666629641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29226687348948412444345709 10960007755855654666629641)
        ·
          refine ⟨8220005816891740999972231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10960007755855654666629641 8220005816891740999972231)
          ·
            refine ⟨12330008725337611499958347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220005816891740999972231 12330008725337611499958347)
            ·
              refine ⟨18495013088006417249937521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12330008725337611499958347 18495013088006417249937521)
              ·
                refine ⟨13871259816004812937453141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18495013088006417249937521 13871259816004812937453141)
                ·
                  refine ⟨162553825968806401610779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13871259816004812937453141 162553825968806401610779)
                  ·
                    rfl

theorem cell21_712288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_712288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712288 prefixEnd_712288 := by exact prefixLift 712288
  have htrace : WordTrace (prefixWord ++ tailWord_712288) baseStart_712288 baseEnd_712288 := by
    simpa [prefixWord, tailWord_712288, baseEnd_712288] using wordTrace_append hprefix tailTrace_712288
  have hstable : (prefixWord ++ tailWord_712288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712288).length < 2 ^ (prefixWord ++ tailWord_712288).sum := by decide
  have hdescent : baseEnd_712288 < baseStart_712288 := by decide
  rcases family_descends (prefixWord ++ tailWord_712288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712353 : List Nat := [1, 2, 3, 3, 2, 3, 2, 5]
def baseStart_712353 : Nat := 118140960795 + 712353 * 2 ^ 59
def prefixEnd_712353 : Nat := 4983230072969 + 3 ^ 40 * 712353 * 2
def baseEnd_712353 : Nat := 54189553284793577675771

theorem tailTrace_712353 : CollatzResearch.WordTrace tailWord_712353 prefixEnd_712353 54189553284793577675771 := by
  unfold tailWord_712353
  simp only [CollatzResearch.WordTrace]
  refine ⟨25981648388274216051645713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17321098925516144034430475 25981648388274216051645713)
  ·
    refine ⟨19486236291205662038734285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25981648388274216051645713 19486236291205662038734285)
    ·
      refine ⟨7307338609202123264525357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19486236291205662038734285 7307338609202123264525357)
      ·
        refine ⟨2740251978450796224197009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7307338609202123264525357 2740251978450796224197009)
        ·
          refine ⟨2055188983838097168147757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2740251978450796224197009 2055188983838097168147757)
          ·
            refine ⟨770695868939286438055409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2055188983838097168147757 770695868939286438055409)
            ·
              refine ⟨578021901704464828541557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770695868939286438055409 578021901704464828541557)
              ·
                refine ⟨54189553284793577675771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 578021901704464828541557 54189553284793577675771)
                ·
                  rfl

theorem cell21_712353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 5].length) (baseStart_712353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712353 prefixEnd_712353 := by exact prefixLift 712353
  have htrace : WordTrace (prefixWord ++ tailWord_712353) baseStart_712353 baseEnd_712353 := by
    simpa [prefixWord, tailWord_712353, baseEnd_712353] using wordTrace_append hprefix tailTrace_712353
  have hstable : (prefixWord ++ tailWord_712353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712353).length < 2 ^ (prefixWord ++ tailWord_712353).sum := by decide
  have hdescent : baseEnd_712353 < baseStart_712353 := by decide
  rcases family_descends (prefixWord ++ tailWord_712353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712381 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 4]
def baseStart_712381 : Nat := 118140960795 + 712381 * 2 ^ 59
def prefixEnd_712381 : Nat := 4983230072969 + 3 ^ 40 * 712381 * 2
def baseEnd_712381 : Nat := 162575049835858906560589

theorem tailTrace_712381 : CollatzResearch.WordTrace tailWord_712381 prefixEnd_712381 162575049835858906560589 := by
  unfold tailWord_712381
  simp only [CollatzResearch.WordTrace]
  refine ⟨25982669632172776833664997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17321779754781851222443331 25982669632172776833664997)
  ·
    refine ⟨4871750556032395656312187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25982669632172776833664997 4871750556032395656312187)
    ·
      refine ⟨7307625834048593484468281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4871750556032395656312187 7307625834048593484468281)
      ·
        refine ⟨5480719375536445113351211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7307625834048593484468281 5480719375536445113351211)
        ·
          refine ⟨8221079063304667670026817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5480719375536445113351211 8221079063304667670026817)
          ·
            refine ⟨6165809297478500752520113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8221079063304667670026817 6165809297478500752520113)
            ·
              refine ⟨4624356973108875564390085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6165809297478500752520113 4624356973108875564390085)
              ·
                refine ⟨867066932457914168323141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4624356973108875564390085 867066932457914168323141)
                ·
                  refine ⟨162575049835858906560589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867066932457914168323141 162575049835858906560589)
                  ·
                    rfl

theorem cell21_712381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_712381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712381 prefixEnd_712381 := by exact prefixLift 712381
  have htrace : WordTrace (prefixWord ++ tailWord_712381) baseStart_712381 baseEnd_712381 := by
    simpa [prefixWord, tailWord_712381, baseEnd_712381] using wordTrace_append hprefix tailTrace_712381
  have hstable : (prefixWord ++ tailWord_712381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712381).length < 2 ^ (prefixWord ++ tailWord_712381).sum := by decide
  have hdescent : baseEnd_712381 < baseStart_712381 := by decide
  rcases family_descends (prefixWord ++ tailWord_712381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712384 : List Nat := [2, 1, 1, 2, 4, 1, 5, 2, 3]
def baseStart_712384 : Nat := 118140960795 + 712384 * 2 ^ 59
def prefixEnd_712384 : Nat := 4983230072969 + 3 ^ 40 * 712384 * 2
def baseEnd_712384 : Nat := 162575734476731568010583

theorem tailTrace_712384 : CollatzResearch.WordTrace tailWord_712384 prefixEnd_712384 162575734476731568010583 := by
  unfold tailWord_712384
  simp only [CollatzResearch.WordTrace]
  refine ⟨12991389525580954173012103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17321852700774605564016137 12991389525580954173012103)
  ·
    refine ⟨19487084288371431259518155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12991389525580954173012103 19487084288371431259518155)
    ·
      refine ⟨29230626432557146889277233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19487084288371431259518155 29230626432557146889277233)
      ·
        refine ⟨21922969824417860166957925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29230626432557146889277233 21922969824417860166957925)
        ·
          refine ⟨4110556842078348781304611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21922969824417860166957925 4110556842078348781304611)
          ·
            refine ⟨6165835263117523171956917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110556842078348781304611 6165835263117523171956917)
            ·
              refine ⟨578047055917267797370961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6165835263117523171956917 578047055917267797370961)
              ·
                refine ⟨433535291937950848028221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578047055917267797370961 433535291937950848028221)
                ·
                  refine ⟨162575734476731568010583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433535291937950848028221 162575734476731568010583)
                  ·
                    rfl

theorem cell21_712384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_712384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712384 prefixEnd_712384 := by exact prefixLift 712384
  have htrace : WordTrace (prefixWord ++ tailWord_712384) baseStart_712384 baseEnd_712384 := by
    simpa [prefixWord, tailWord_712384, baseEnd_712384] using wordTrace_append hprefix tailTrace_712384
  have hstable : (prefixWord ++ tailWord_712384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712384).length < 2 ^ (prefixWord ++ tailWord_712384).sum := by decide
  have hdescent : baseEnd_712384 < baseStart_712384 := by decide
  rcases family_descends (prefixWord ++ tailWord_712384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712446 : List Nat := [4, 2, 2, 1, 4, 1, 1, 6]
def baseStart_712446 : Nat := 118140960795 + 712446 * 2 ^ 59
def prefixEnd_712446 : Nat := 4983230072969 + 3 ^ 40 * 712446 * 2
def baseEnd_712446 : Nat := 54196627907144412659041

theorem tailTrace_712446 : CollatzResearch.WordTrace tailWord_712446 prefixEnd_712446 54196627907144412659041 := by
  unfold tailWord_712446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248130047117161616847649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17323360251291528623187461 3248130047117161616847649)
  ·
    refine ⟨2436097535337871212635737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3248130047117161616847649 2436097535337871212635737)
    ·
      refine ⟨1827073151503403409476803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2436097535337871212635737 1827073151503403409476803)
      ·
        refine ⟨2740609727255105114215205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827073151503403409476803 2740609727255105114215205)
        ·
          refine ⟨513864323860332208915351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2740609727255105114215205 513864323860332208915351)
          ·
            refine ⟨770796485790498313373027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513864323860332208915351 770796485790498313373027)
            ·
              refine ⟨1156194728685747470059541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770796485790498313373027 1156194728685747470059541)
              ·
                refine ⟨54196627907144412659041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1156194728685747470059541 54196627907144412659041)
                ·
                  rfl

theorem cell21_712446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_712446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712446 prefixEnd_712446 := by exact prefixLift 712446
  have htrace : WordTrace (prefixWord ++ tailWord_712446) baseStart_712446 baseEnd_712446 := by
    simpa [prefixWord, tailWord_712446, baseEnd_712446] using wordTrace_append hprefix tailTrace_712446
  have hstable : (prefixWord ++ tailWord_712446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712446).length < 2 ^ (prefixWord ++ tailWord_712446).sum := by decide
  have hdescent : baseEnd_712446 < baseStart_712446 := by decide
  rcases family_descends (prefixWord ++ tailWord_712446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712598 : List Nat := [5, 3, 1, 1, 3, 8]
def baseStart_712598 : Nat := 118140960795 + 712598 * 2 ^ 59
def prefixEnd_712598 : Nat := 4983230072969 + 3 ^ 40 * 712598 * 2
def baseEnd_712598 : Nat := 6023132303419064868277

theorem tailTrace_712598 : CollatzResearch.WordTrace tailWord_712598 prefixEnd_712598 6023132303419064868277 := by
  unfold tailWord_712598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624411517024163930894653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17327056181591081929542965 1624411517024163930894653)
  ·
    refine ⟨609154318884061474085495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1624411517024163930894653 609154318884061474085495)
    ·
      refine ⟨913731478326092211128243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 609154318884061474085495 913731478326092211128243)
      ·
        refine ⟨1370597217489138316692365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913731478326092211128243 1370597217489138316692365)
        ·
          refine ⟨513973956558426868759637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1370597217489138316692365 513973956558426868759637)
          ·
            refine ⟨6023132303419064868277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 513973956558426868759637 6023132303419064868277)
            ·
              rfl

theorem cell21_712598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 8].length) (baseStart_712598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712598 prefixEnd_712598 := by exact prefixLift 712598
  have htrace : WordTrace (prefixWord ++ tailWord_712598) baseStart_712598 baseEnd_712598 := by
    simpa [prefixWord, tailWord_712598, baseEnd_712598] using wordTrace_append hprefix tailTrace_712598
  have hstable : (prefixWord ++ tailWord_712598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712598).length < 2 ^ (prefixWord ++ tailWord_712598).sum := by decide
  have hdescent : baseEnd_712598 < baseStart_712598 := by decide
  rcases family_descends (prefixWord ++ tailWord_712598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712612 : List Nat := [2, 3, 1, 2, 1, 3, 4, 2, 3]
def baseStart_712612 : Nat := 118140960795 + 712612 * 2 ^ 59
def prefixEnd_712612 : Nat := 4983230072969 + 3 ^ 40 * 712612 * 2
def baseEnd_712612 : Nat := 162627767183053838210117

theorem tailTrace_712612 : CollatzResearch.WordTrace tailWord_712612 prefixEnd_712612 162627767183053838210117 := by
  unfold tailWord_712612
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995547447167951642662045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17327396596223935523549393 12995547447167951642662045)
  ·
    refine ⟨4873330292687981865998267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12995547447167951642662045 4873330292687981865998267)
    ·
      refine ⟨7309995439031972798997401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4873330292687981865998267 7309995439031972798997401)
      ·
        refine ⟨5482496579273979599248051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7309995439031972798997401 5482496579273979599248051)
        ·
          refine ⟨8223744868910969398872077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5482496579273979599248051 8223744868910969398872077)
          ·
            refine ⟨3083904325841613524577029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8223744868910969398872077 3083904325841613524577029)
            ·
              refine ⟨578232061095302535858193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3083904325841613524577029 578232061095302535858193)
              ·
                refine ⟨433674045821476901893645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578232061095302535858193 433674045821476901893645)
                ·
                  refine ⟨162627767183053838210117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433674045821476901893645 162627767183053838210117)
                  ·
                    rfl

theorem cell21_712612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_712612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712612 prefixEnd_712612 := by exact prefixLift 712612
  have htrace : WordTrace (prefixWord ++ tailWord_712612) baseStart_712612 baseEnd_712612 := by
    simpa [prefixWord, tailWord_712612, baseEnd_712612] using wordTrace_append hprefix tailTrace_712612
  have hstable : (prefixWord ++ tailWord_712612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712612).length < 2 ^ (prefixWord ++ tailWord_712612).sum := by decide
  have hdescent : baseEnd_712612 < baseStart_712612 := by decide
  rcases family_descends (prefixWord ++ tailWord_712612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712671 : List Nat := [1, 1, 2, 3, 4, 1, 2, 4, 3]
def baseStart_712671 : Nat := 118140960795 + 712671 * 2 ^ 59
def prefixEnd_712671 : Nat := 4983230072969 + 3 ^ 40 * 712671 * 2
def baseEnd_712671 : Nat := 162641231786882846726663

theorem tailTrace_712671 : CollatzResearch.WordTrace tailWord_712671 prefixEnd_712671 162641231786882846726663 := by
  unfold tailWord_712671
  simp only [CollatzResearch.WordTrace]
  refine ⟨25993246801122156361721867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17328831200748104241147911 25993246801122156361721867)
  ·
    refine ⟨38989870201683234542582801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25993246801122156361721867 38989870201683234542582801)
    ·
      refine ⟨29242402651262425906937101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38989870201683234542582801 29242402651262425906937101)
      ·
        refine ⟨10965900994223409715101413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29242402651262425906937101 10965900994223409715101413)
        ·
          refine ⟨2056106436416889321581515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10965900994223409715101413 2056106436416889321581515)
          ·
            refine ⟨3084159654625333982372273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056106436416889321581515 3084159654625333982372273)
            ·
              refine ⟨2313119740969000486779205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084159654625333982372273 2313119740969000486779205)
              ·
                refine ⟨433709951431687591271101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2313119740969000486779205 433709951431687591271101)
                ·
                  refine ⟨162641231786882846726663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433709951431687591271101 162641231786882846726663)
                  ·
                    rfl

theorem cell21_712671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 3].length) (baseStart_712671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712671 prefixEnd_712671 := by exact prefixLift 712671
  have htrace : WordTrace (prefixWord ++ tailWord_712671) baseStart_712671 baseEnd_712671 := by
    simpa [prefixWord, tailWord_712671, baseEnd_712671] using wordTrace_append hprefix tailTrace_712671
  have hstable : (prefixWord ++ tailWord_712671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712671).length < 2 ^ (prefixWord ++ tailWord_712671).sum := by decide
  have hdescent : baseEnd_712671 < baseStart_712671 := by decide
  rcases family_descends (prefixWord ++ tailWord_712671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712699 : List Nat := [1, 1, 1, 1, 1, 3, 8, 5]
def baseStart_712699 : Nat := 118140960795 + 712699 * 2 ^ 59
def prefixEnd_712699 : Nat := 4983230072969 + 3 ^ 40 * 712699 * 2
def baseEnd_712699 : Nat := 54215873922787006753313

theorem tailTrace_712699 : CollatzResearch.WordTrace tailWord_712699 prefixEnd_712699 54215873922787006753313 := by
  unfold tailWord_712699
  simp only [CollatzResearch.WordTrace]
  refine ⟨25994268045020717143741151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17329512030013811429160767 25994268045020717143741151)
  ·
    refine ⟨38991402067531075715611727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25994268045020717143741151 38991402067531075715611727)
    ·
      refine ⟨58487103101296613573417591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38991402067531075715611727 58487103101296613573417591)
      ·
        refine ⟨87730654651944920360126387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58487103101296613573417591 87730654651944920360126387)
        ·
          refine ⟨131595981977917380540189581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87730654651944920360126387 131595981977917380540189581)
          ·
            refine ⟨49348493241719017702571093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131595981977917380540189581 49348493241719017702571093)
            ·
              refine ⟨578302655176394738702005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 49348493241719017702571093 578302655176394738702005)
              ·
                refine ⟨54215873922787006753313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 578302655176394738702005 54215873922787006753313)
                ·
                  rfl

theorem cell21_712699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 5].length) (baseStart_712699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712699 prefixEnd_712699 := by exact prefixLift 712699
  have htrace : WordTrace (prefixWord ++ tailWord_712699) baseStart_712699 baseEnd_712699 := by
    simpa [prefixWord, tailWord_712699, baseEnd_712699] using wordTrace_append hprefix tailTrace_712699
  have hstable : (prefixWord ++ tailWord_712699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712699).length < 2 ^ (prefixWord ++ tailWord_712699).sum := by decide
  have hdescent : baseEnd_712699 < baseStart_712699 := by decide
  rcases family_descends (prefixWord ++ tailWord_712699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712730 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_712730 : Nat := 118140960795 + 712730 * 2 ^ 59
def prefixEnd_712730 : Nat := 4983230072969 + 3 ^ 40 * 712730 * 2
def baseEnd_712730 : Nat := 162654696390711855243209

theorem tailTrace_712730 : CollatzResearch.WordTrace tailWord_712730 prefixEnd_712730 162654696390711855243209 := by
  unfold tailWord_712730
  simp only [CollatzResearch.WordTrace]
  refine ⟨6498849676977102359529911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17330265805272272958746429 6498849676977102359529911)
  ·
    refine ⟨9748274515465653539294867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6498849676977102359529911 9748274515465653539294867)
    ·
      refine ⟨14622411773198480308942301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9748274515465653539294867 14622411773198480308942301)
      ·
        refine ⟨5483404414949430115853363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14622411773198480308942301 5483404414949430115853363)
        ·
          refine ⟨8225106622424145173780045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483404414949430115853363 8225106622424145173780045)
          ·
            refine ⟨3084414983409054440167517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8225106622424145173780045 3084414983409054440167517)
            ·
              refine ⟨1156655618778395415062819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3084414983409054440167517 1156655618778395415062819)
              ·
                refine ⟨1734983428167593122594229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156655618778395415062819 1734983428167593122594229)
                ·
                  refine ⟨162654696390711855243209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1734983428167593122594229 162654696390711855243209)
                  ·
                    rfl

theorem cell21_712730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_712730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712730 prefixEnd_712730 := by exact prefixLift 712730
  have htrace : WordTrace (prefixWord ++ tailWord_712730) baseStart_712730 baseEnd_712730 := by
    simpa [prefixWord, tailWord_712730, baseEnd_712730] using wordTrace_append hprefix tailTrace_712730
  have hstable : (prefixWord ++ tailWord_712730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712730).length < 2 ^ (prefixWord ++ tailWord_712730).sum := by decide
  have hdescent : baseEnd_712730 < baseStart_712730 := by decide
  rcases family_descends (prefixWord ++ tailWord_712730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712823 : List Nat := [1, 1, 3, 1, 1, 6, 2, 3, 3]
def baseStart_712823 : Nat := 118140960795 + 712823 * 2 ^ 59
def prefixEnd_712823 : Nat := 4983230072969 + 3 ^ 40 * 712823 * 2
def baseEnd_712823 : Nat := 162675920257764360193019

theorem tailTrace_712823 : CollatzResearch.WordTrace tailWord_712823 prefixEnd_712823 162675920257764360193019 := by
  unfold tailWord_712823
  simp only [CollatzResearch.WordTrace]
  refine ⟨25998790696571486321255123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17332527131047657547503415 25998790696571486321255123)
  ·
    refine ⟨38998186044857229481882685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25998790696571486321255123 38998186044857229481882685)
    ·
      refine ⟨14624319766821461055706007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38998186044857229481882685 14624319766821461055706007)
      ·
        refine ⟨21936479650232191583559011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14624319766821461055706007 21936479650232191583559011)
        ·
          refine ⟨32904719475348287375338517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21936479650232191583559011 32904719475348287375338517)
          ·
            refine ⟨1542408725406950970718993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32904719475348287375338517 1542408725406950970718993)
            ·
              refine ⟨1156806544055213228039245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1542408725406950970718993 1156806544055213228039245)
              ·
                refine ⟨433802454020704960514717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1156806544055213228039245 433802454020704960514717)
                ·
                  refine ⟨162675920257764360193019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433802454020704960514717 162675920257764360193019)
                  ·
                    rfl

theorem cell21_712823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 3].length) (baseStart_712823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712823 prefixEnd_712823 := by exact prefixLift 712823
  have htrace : WordTrace (prefixWord ++ tailWord_712823) baseStart_712823 baseEnd_712823 := by
    simpa [prefixWord, tailWord_712823, baseEnd_712823] using wordTrace_append hprefix tailTrace_712823
  have hstable : (prefixWord ++ tailWord_712823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712823).length < 2 ^ (prefixWord ++ tailWord_712823).sum := by decide
  have hdescent : baseEnd_712823 < baseStart_712823 := by decide
  rcases family_descends (prefixWord ++ tailWord_712823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712837 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 4]
def baseStart_712837 : Nat := 118140960795 + 712837 * 2 ^ 59
def prefixEnd_712837 : Nat := 4983230072969 + 3 ^ 40 * 712837 * 2
def baseEnd_712837 : Nat := 162679115248503446959657

theorem tailTrace_712837 : CollatzResearch.WordTrace tailWord_712837 prefixEnd_712837 162679115248503446959657 := by
  unfold tailWord_712837
  simp only [CollatzResearch.WordTrace]
  refine ⟨25999301318520766712264765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17332867545680511141509843 25999301318520766712264765)
  ·
    refine ⟨9749737994445287517099287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25999301318520766712264765 9749737994445287517099287)
    ·
      refine ⟨14624606991667931275648931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9749737994445287517099287 14624606991667931275648931)
      ·
        refine ⟨21936910487501896913473397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14624606991667931275648931 21936910487501896913473397)
        ·
          refine ⟨2056585358203302835638131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21936910487501896913473397 2056585358203302835638131)
          ·
            refine ⟨3084878037304954253457197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056585358203302835638131 3084878037304954253457197)
            ·
              refine ⟨1156829263989357845046449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3084878037304954253457197 1156829263989357845046449)
              ·
                refine ⟨867621947992018383784837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1156829263989357845046449 867621947992018383784837)
                ·
                  refine ⟨162679115248503446959657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867621947992018383784837 162679115248503446959657)
                  ·
                    rfl

theorem cell21_712837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_712837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712837 prefixEnd_712837 := by exact prefixLift 712837
  have htrace : WordTrace (prefixWord ++ tailWord_712837) baseStart_712837 baseEnd_712837 := by
    simpa [prefixWord, tailWord_712837, baseEnd_712837] using wordTrace_append hprefix tailTrace_712837
  have hstable : (prefixWord ++ tailWord_712837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712837).length < 2 ^ (prefixWord ++ tailWord_712837).sum := by decide
  have hdescent : baseEnd_712837 < baseStart_712837 := by decide
  rcases family_descends (prefixWord ++ tailWord_712837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712874 : List Nat := [3, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_712874 : Nat := 118140960795 + 712874 * 2 ^ 59
def prefixEnd_712874 : Nat := 4983230072969 + 3 ^ 40 * 712874 * 2
def baseEnd_712874 : Nat := 162687559152599604842915

theorem tailTrace_712874 : CollatzResearch.WordTrace tailWord_712874 prefixEnd_712874 162687559152599604842915 := by
  unfold tailWord_712874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500162704846680507840419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17333767212924481354241117 6500162704846680507840419)
  ·
    refine ⟨9750244057270020761760629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6500162704846680507840419 9750244057270020761760629)
    ·
      refine ⟨914085380369064446415059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9750244057270020761760629 914085380369064446415059)
      ·
        refine ⟨1371128070553596669622589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914085380369064446415059 1371128070553596669622589)
        ·
          refine ⟨514173026457598751108471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1371128070553596669622589 514173026457598751108471)
          ·
            refine ⟨771259539686398126662707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514173026457598751108471 771259539686398126662707)
            ·
              refine ⟨1156889309529597189994061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771259539686398126662707 1156889309529597189994061)
              ·
                refine ⟨433833491073598946247773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1156889309529597189994061 433833491073598946247773)
                ·
                  refine ⟨162687559152599604842915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433833491073598946247773 162687559152599604842915)
                  ·
                    rfl

theorem cell21_712874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_712874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712874 prefixEnd_712874 := by exact prefixLift 712874
  have htrace : WordTrace (prefixWord ++ tailWord_712874) baseStart_712874 baseEnd_712874 := by
    simpa [prefixWord, tailWord_712874, baseEnd_712874] using wordTrace_append hprefix tailTrace_712874
  have hstable : (prefixWord ++ tailWord_712874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712874).length < 2 ^ (prefixWord ++ tailWord_712874).sum := by decide
  have hdescent : baseEnd_712874 < baseStart_712874 := by decide
  rcases family_descends (prefixWord ++ tailWord_712874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712885 : List Nat := [1, 3, 3, 4, 2, 1, 7]
def baseStart_712885 : Nat := 118140960795 + 712885 * 2 ^ 59
def prefixEnd_712885 : Nat := 4983230072969 + 3 ^ 40 * 712885 * 2
def baseEnd_712885 : Nat := 18076674389162892239951

theorem tailTrace_712885 : CollatzResearch.WordTrace tailWord_712885 prefixEnd_712885 18076674389162892239951 := by
  unfold tailWord_712885
  simp only [CollatzResearch.WordTrace]
  refine ⟨26001052022346870910012109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17334034681564580606674739 26001052022346870910012109)
  ·
    refine ⟨9750394508380076591254541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26001052022346870910012109 9750394508380076591254541)
    ·
      refine ⟨3656397940642528721720453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9750394508380076591254541 3656397940642528721720453)
      ·
        refine ⟨685574613870474135322585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3656397940642528721720453 685574613870474135322585)
        ·
          refine ⟨514180960402855601491939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685574613870474135322585 514180960402855601491939)
          ·
            refine ⟨771271440604283402237909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514180960402855601491939 771271440604283402237909)
            ·
              refine ⟨18076674389162892239951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 771271440604283402237909 18076674389162892239951)
              ·
                rfl

theorem cell21_712885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 7].length) (baseStart_712885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712885 prefixEnd_712885 := by exact prefixLift 712885
  have htrace : WordTrace (prefixWord ++ tailWord_712885) baseStart_712885 baseEnd_712885 := by
    simpa [prefixWord, tailWord_712885, baseEnd_712885] using wordTrace_append hprefix tailTrace_712885
  have hstable : (prefixWord ++ tailWord_712885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712885).length < 2 ^ (prefixWord ++ tailWord_712885).sum := by decide
  have hdescent : baseEnd_712885 < baseStart_712885 := by decide
  rcases family_descends (prefixWord ++ tailWord_712885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712896 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_712896 : Nat := 118140960795 + 712896 * 2 ^ 59
def prefixEnd_712896 : Nat := 4983230072969 + 3 ^ 40 * 712896 * 2
def baseEnd_712896 : Nat := 162692579852332455476203

theorem tailTrace_712896 : CollatzResearch.WordTrace tailWord_712896 prefixEnd_712896 162692579852332455476203 := by
  unfold tailWord_712896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13000726612653509894331271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17334302150204679859108361 13000726612653509894331271)
  ·
    refine ⟨19501089918980264841496907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13000726612653509894331271 19501089918980264841496907)
    ·
      refine ⟨29251634878470397262245361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19501089918980264841496907 29251634878470397262245361)
      ·
        refine ⟨21938726158852797946684021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29251634878470397262245361 21938726158852797946684021)
        ·
          refine ⟨2056755577392449807501627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21938726158852797946684021 2056755577392449807501627)
          ·
            refine ⟨3085133366088674711252441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056755577392449807501627 3085133366088674711252441)
            ·
              refine ⟨2313850024566506033439331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3085133366088674711252441 2313850024566506033439331)
              ·
                refine ⟨3470775036849759050158997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313850024566506033439331 3470775036849759050158997)
                ·
                  refine ⟨162692579852332455476203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3470775036849759050158997 162692579852332455476203)
                  ·
                    rfl

theorem cell21_712896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_712896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712896 prefixEnd_712896 := by exact prefixLift 712896
  have htrace : WordTrace (prefixWord ++ tailWord_712896) baseStart_712896 baseEnd_712896 := by
    simpa [prefixWord, tailWord_712896, baseEnd_712896] using wordTrace_append hprefix tailTrace_712896
  have hstable : (prefixWord ++ tailWord_712896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712896).length < 2 ^ (prefixWord ++ tailWord_712896).sum := by decide
  have hdescent : baseEnd_712896 < baseStart_712896 := by decide
  rcases family_descends (prefixWord ++ tailWord_712896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712913 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 4]
def baseStart_712913 : Nat := 118140960795 + 712913 * 2 ^ 59
def prefixEnd_712913 : Nat := 4983230072969 + 3 ^ 40 * 712913 * 2
def baseEnd_712913 : Nat := 162696459483944203692835

theorem tailTrace_712913 : CollatzResearch.WordTrace tailWord_712913 prefixEnd_712913 162696459483944203692835 := by
  unfold tailWord_712913
  simp only [CollatzResearch.WordTrace]
  refine ⟨26002073266245431692031393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17334715510830287794687595 26002073266245431692031393)
  ·
    refine ⟨19501554949684073769023545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26002073266245431692031393 19501554949684073769023545)
    ·
      refine ⟨14626166212263055326767659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19501554949684073769023545 14626166212263055326767659)
      ·
        refine ⟨21939249318394582990151489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14626166212263055326767659 21939249318394582990151489)
        ·
          refine ⟨16454436988795937242613617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21939249318394582990151489 16454436988795937242613617)
          ·
            refine ⟨12340827741596952931960213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16454436988795937242613617 12340827741596952931960213)
            ·
              refine ⟨578476300387357168685635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12340827741596952931960213 578476300387357168685635)
              ·
                refine ⟨867714450581035753028453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578476300387357168685635 867714450581035753028453)
                ·
                  refine ⟨162696459483944203692835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867714450581035753028453 162696459483944203692835)
                  ·
                    rfl

theorem cell21_712913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_712913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712913 prefixEnd_712913 := by exact prefixLift 712913
  have htrace : WordTrace (prefixWord ++ tailWord_712913) baseStart_712913 baseEnd_712913 := by
    simpa [prefixWord, tailWord_712913, baseEnd_712913] using wordTrace_append hprefix tailTrace_712913
  have hstable : (prefixWord ++ tailWord_712913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712913).length < 2 ^ (prefixWord ++ tailWord_712913).sum := by decide
  have hdescent : baseEnd_712913 < baseStart_712913 := by decide
  rcases family_descends (prefixWord ++ tailWord_712913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712958 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_712958 : Nat := 118140960795 + 712958 * 2 ^ 59
def prefixEnd_712958 : Nat := 4983230072969 + 3 ^ 40 * 712958 * 2
def baseEnd_712958 : Nat := 162706729097034125442743

theorem tailTrace_712958 : CollatzResearch.WordTrace tailWord_712958 prefixEnd_712958 162706729097034125442743 := by
  unfold tailWord_712958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250464318885300547177441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17335809700721602918279685 3250464318885300547177441)
  ·
    refine ⟨2437848239163975410383081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3250464318885300547177441 2437848239163975410383081)
    ·
      refine ⟨1828386179372981557787311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2437848239163975410383081 1828386179372981557787311)
      ·
        refine ⟨2742579269059472336680967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828386179372981557787311 2742579269059472336680967)
        ·
          refine ⟨4113868903589208505021451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742579269059472336680967 4113868903589208505021451)
          ·
            refine ⟨6170803355383812757532177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113868903589208505021451 6170803355383812757532177)
            ·
              refine ⟨4628102516537859568149133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6170803355383812757532177 4628102516537859568149133)
              ·
                refine ⟨1735538443701697338055925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4628102516537859568149133 1735538443701697338055925)
                ·
                  refine ⟨162706729097034125442743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1735538443701697338055925 162706729097034125442743)
                  ·
                    rfl

theorem cell21_712958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_712958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712958 prefixEnd_712958 := by exact prefixLift 712958
  have htrace : WordTrace (prefixWord ++ tailWord_712958) baseStart_712958 baseEnd_712958 := by
    simpa [prefixWord, tailWord_712958, baseEnd_712958] using wordTrace_append hprefix tailTrace_712958
  have hstable : (prefixWord ++ tailWord_712958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712958).length < 2 ^ (prefixWord ++ tailWord_712958).sum := by decide
  have hdescent : baseEnd_712958 < baseStart_712958 := by decide
  rcases family_descends (prefixWord ++ tailWord_712958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712972 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_712972 : Nat := 118140960795 + 712972 * 2 ^ 59
def prefixEnd_712972 : Nat := 4983230072969 + 3 ^ 40 * 712972 * 2
def baseEnd_712972 : Nat := 162709924087773212209381

theorem tailTrace_712972 : CollatzResearch.WordTrace tailWord_712972 prefixEnd_712972 162709924087773212209381 := by
  unfold tailWord_712972
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002112586515842384214585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17336150115354456512286113 13002112586515842384214585)
  ·
    refine ⟨9751584439886881788160939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13002112586515842384214585 9751584439886881788160939)
    ·
      refine ⟨14627376659830322682241409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9751584439886881788160939 14627376659830322682241409)
      ·
        refine ⟨10970532494872742011681057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14627376659830322682241409 10970532494872742011681057)
        ·
          refine ⟨8227899371154556508760793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10970532494872742011681057 8227899371154556508760793)
          ·
            refine ⟨6170924528365917381570595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8227899371154556508760793 6170924528365917381570595)
            ·
              refine ⟨9256386792548876072355893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6170924528365917381570595 9256386792548876072355893)
              ·
                refine ⟨867786261801457131783365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9256386792548876072355893 867786261801457131783365)
                ·
                  refine ⟨162709924087773212209381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867786261801457131783365 162709924087773212209381)
                  ·
                    rfl

theorem cell21_712972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_712972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_712972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_712972 prefixEnd_712972 := by exact prefixLift 712972
  have htrace : WordTrace (prefixWord ++ tailWord_712972) baseStart_712972 baseEnd_712972 := by
    simpa [prefixWord, tailWord_712972, baseEnd_712972] using wordTrace_append hprefix tailTrace_712972
  have hstable : (prefixWord ++ tailWord_712972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712972).length < 2 ^ (prefixWord ++ tailWord_712972).sum := by decide
  have hdescent : baseEnd_712972 < baseStart_712972 := by decide
  rcases family_descends (prefixWord ++ tailWord_712972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713006 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_713006 : Nat := 118140960795 + 713006 * 2 ^ 59
def prefixEnd_713006 : Nat := 4983230072969 + 3 ^ 40 * 713006 * 2
def baseEnd_713006 : Nat := 162717683350996708642645

theorem tailTrace_713006 : CollatzResearch.WordTrace tailWord_713006 prefixEnd_713006 162717683350996708642645 := by
  unfold tailWord_713006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250683156863563571895859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17336976836605672383444581 3250683156863563571895859)
  ·
    refine ⟨4876024735295345357843789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3250683156863563571895859 4876024735295345357843789)
    ·
      refine ⟨1828509275735754509191421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4876024735295345357843789 1828509275735754509191421)
      ·
        refine ⟨685690978400907940946783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1828509275735754509191421 685690978400907940946783)
        ·
          refine ⟨1028536467601361911420175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685690978400907940946783 1028536467601361911420175)
          ·
            refine ⟨1542804701402042867130263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028536467601361911420175 1542804701402042867130263)
            ·
              refine ⟨2314207052103064300695395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542804701402042867130263 2314207052103064300695395)
              ·
                refine ⟨3471310578154596451043093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314207052103064300695395 3471310578154596451043093)
                ·
                  refine ⟨162717683350996708642645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3471310578154596451043093 162717683350996708642645)
                  ·
                    rfl

theorem cell21_713006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_713006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713006 prefixEnd_713006 := by exact prefixLift 713006
  have htrace : WordTrace (prefixWord ++ tailWord_713006) baseStart_713006 baseEnd_713006 := by
    simpa [prefixWord, tailWord_713006, baseEnd_713006] using wordTrace_append hprefix tailTrace_713006
  have hstable : (prefixWord ++ tailWord_713006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713006).length < 2 ^ (prefixWord ++ tailWord_713006).sum := by decide
  have hdescent : baseEnd_713006 < baseStart_713006 := by decide
  rcases family_descends (prefixWord ++ tailWord_713006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713068 : List Nat := [2, 2, 1, 1, 6, 1, 3, 2, 3]
def baseStart_713068 : Nat := 118140960795 + 713068 * 2 ^ 59
def prefixEnd_713068 : Nat := 4983230072969 + 3 ^ 40 * 713068 * 2
def baseEnd_713068 : Nat := 162731832595698378609185

theorem tailTrace_713068 : CollatzResearch.WordTrace tailWord_713068 prefixEnd_713068 162731832595698378609185 := by
  unfold tailWord_713068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003863290341946581961929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17338484387122595442615905 13003863290341946581961929)
  ·
    refine ⟨9752897467756459936471447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13003863290341946581961929 9752897467756459936471447)
    ·
      refine ⟨14629346201634689904707171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9752897467756459936471447 14629346201634689904707171)
      ·
        refine ⟨21944019302452034857060757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14629346201634689904707171 21944019302452034857060757)
        ·
          refine ⟨1028625904802439133924723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21944019302452034857060757 1028625904802439133924723)
          ·
            refine ⟨1542938857203658700887085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028625904802439133924723 1542938857203658700887085)
            ·
              refine ⟨578602071451372012832657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1542938857203658700887085 578602071451372012832657)
              ·
                refine ⟨433951553588529009624493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578602071451372012832657 433951553588529009624493)
                ·
                  refine ⟨162731832595698378609185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433951553588529009624493 162731832595698378609185)
                  ·
                    rfl

theorem cell21_713068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_713068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713068 prefixEnd_713068 := by exact prefixLift 713068
  have htrace : WordTrace (prefixWord ++ tailWord_713068) baseStart_713068 baseEnd_713068 := by
    simpa [prefixWord, tailWord_713068, baseEnd_713068] using wordTrace_append hprefix tailTrace_713068
  have hstable : (prefixWord ++ tailWord_713068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713068).length < 2 ^ (prefixWord ++ tailWord_713068).sum := by decide
  have hdescent : baseEnd_713068 < baseStart_713068 := by decide
  rcases family_descends (prefixWord ++ tailWord_713068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713124 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_713124 : Nat := 118140960795 + 713124 * 2 ^ 59
def prefixEnd_713124 : Nat := 4983230072969 + 3 ^ 40 * 713124 * 2
def baseEnd_713124 : Nat := 162744612558654725675737

theorem tailTrace_713124 : CollatzResearch.WordTrace tailWord_713124 prefixEnd_713124 162744612558654725675737 := by
  unfold tailWord_713124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004884534240507363981213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17339846045654009818641617 13004884534240507363981213)
  ·
    refine ⟨4876831700340190261492955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13004884534240507363981213 4876831700340190261492955)
    ·
      refine ⟨7315247550510285392239433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876831700340190261492955 7315247550510285392239433)
      ·
        refine ⟨5486435662882714044179575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7315247550510285392239433 5486435662882714044179575)
        ·
          refine ⟨8229653494324071066269363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486435662882714044179575 8229653494324071066269363)
          ·
            refine ⟨12344480241486106599404045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8229653494324071066269363 12344480241486106599404045)
            ·
              refine ⟨4629180090557289974776517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12344480241486106599404045 4629180090557289974776517)
              ·
                refine ⟨867971266979491870270597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4629180090557289974776517 867971266979491870270597)
                ·
                  refine ⟨162744612558654725675737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867971266979491870270597 162744612558654725675737)
                  ·
                    rfl

theorem cell21_713124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_713124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713124 prefixEnd_713124 := by exact prefixLift 713124
  have htrace : WordTrace (prefixWord ++ tailWord_713124) baseStart_713124 baseEnd_713124 := by
    simpa [prefixWord, tailWord_713124, baseEnd_713124] using wordTrace_append hprefix tailTrace_713124
  have hstable : (prefixWord ++ tailWord_713124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713124).length < 2 ^ (prefixWord ++ tailWord_713124).sum := by decide
  have hdescent : baseEnd_713124 < baseStart_713124 := by decide
  rcases family_descends (prefixWord ++ tailWord_713124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713127 : List Nat := [1, 1, 6, 1, 1, 3, 1, 4, 3]
def baseStart_713127 : Nat := 118140960795 + 713127 * 2 ^ 59
def prefixEnd_713127 : Nat := 4983230072969 + 3 ^ 40 * 713127 * 2
def baseEnd_713127 : Nat := 162745297199527387125731

theorem tailTrace_713127 : CollatzResearch.WordTrace tailWord_713127 prefixEnd_713127 162745297199527387125731 := by
  unfold tailWord_713127
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009878487470146240321635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17339918991646764160214423 26009878487470146240321635)
  ·
    refine ⟨39014817731205219360482453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26009878487470146240321635 39014817731205219360482453)
    ·
      refine ⟨1828819581150244657522615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39014817731205219360482453 1828819581150244657522615)
      ·
        refine ⟨2743229371725366986283923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828819581150244657522615 2743229371725366986283923)
        ·
          refine ⟨4114844057588050479425885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743229371725366986283923 4114844057588050479425885)
          ·
            refine ⟨1543066521595518929784707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4114844057588050479425885 1543066521595518929784707)
            ·
              refine ⟨2314599782393278394677061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543066521595518929784707 2314599782393278394677061)
              ·
                refine ⟨433987459198739699001949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2314599782393278394677061 433987459198739699001949)
                ·
                  refine ⟨162745297199527387125731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433987459198739699001949 162745297199527387125731)
                  ·
                    rfl

theorem cell21_713127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 3].length) (baseStart_713127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713127 prefixEnd_713127 := by exact prefixLift 713127
  have htrace : WordTrace (prefixWord ++ tailWord_713127) baseStart_713127 baseEnd_713127 := by
    simpa [prefixWord, tailWord_713127, baseEnd_713127] using wordTrace_append hprefix tailTrace_713127
  have hstable : (prefixWord ++ tailWord_713127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713127).length < 2 ^ (prefixWord ++ tailWord_713127).sum := by decide
  have hdescent : baseEnd_713127 < baseStart_713127 := by decide
  rcases family_descends (prefixWord ++ tailWord_713127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713130 : List Nat := [3, 1, 6, 1, 1, 2, 1, 6]
def baseStart_713130 : Nat := 118140960795 + 713130 * 2 ^ 59
def prefixEnd_713130 : Nat := 4983230072969 + 3 ^ 40 * 713130 * 2
def baseEnd_713130 : Nat := 54248660613466682858575

theorem tailTrace_713130 : CollatzResearch.WordTrace tailWord_713130 prefixEnd_713130 54248660613466682858575 := by
  unfold tailWord_713130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6502496976614819438170211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17339991937639518501787229 6502496976614819438170211)
  ·
    refine ⟨9753745464922229157255317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6502496976614819438170211 9753745464922229157255317)
    ·
      refine ⟨457206818668229491746343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9753745464922229157255317 457206818668229491746343)
      ·
        refine ⟨685810228002344237619515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457206818668229491746343 685810228002344237619515)
        ·
          refine ⟨1028715342003516356429273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685810228002344237619515 1028715342003516356429273)
          ·
            refine ⟨771536506502637267321955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028715342003516356429273 771536506502637267321955)
            ·
              refine ⟨1157304759753955900982933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771536506502637267321955 1157304759753955900982933)
              ·
                refine ⟨54248660613466682858575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1157304759753955900982933 54248660613466682858575)
                ·
                  rfl

theorem cell21_713130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_713130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713130 prefixEnd_713130 := by exact prefixLift 713130
  have htrace : WordTrace (prefixWord ++ tailWord_713130) baseStart_713130 baseEnd_713130 := by
    simpa [prefixWord, tailWord_713130, baseEnd_713130] using wordTrace_append hprefix tailTrace_713130
  have hstable : (prefixWord ++ tailWord_713130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713130).length < 2 ^ (prefixWord ++ tailWord_713130).sum := by decide
  have hdescent : baseEnd_713130 < baseStart_713130 := by decide
  rcases family_descends (prefixWord ++ tailWord_713130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713220 : List Nat := [2, 3, 2, 3, 1, 3, 1, 3, 3]
def baseStart_713220 : Nat := 118140960795 + 713220 * 2 ^ 59
def prefixEnd_713220 : Nat := 4983230072969 + 3 ^ 40 * 713220 * 2
def baseEnd_713220 : Nat := 162766521066579892075541

theorem tailTrace_713220 : CollatzResearch.WordTrace tailWord_713220 prefixEnd_713220 162766521066579892075541 := by
  unfold tailWord_713220
  simp only [CollatzResearch.WordTrace]
  refine ⟨13006635238066611561728557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17342180317422148748971409 13006635238066611561728557)
  ·
    refine ⟨4877488214274979335648209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13006635238066611561728557 4877488214274979335648209)
    ·
      refine ⟨3658116160706234501736157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4877488214274979335648209 3658116160706234501736157)
      ·
        refine ⟨1371793560264837938151059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3658116160706234501736157 1371793560264837938151059)
        ·
          refine ⟨2057690340397256907226589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371793560264837938151059 2057690340397256907226589)
          ·
            refine ⟨771633877648971340209971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2057690340397256907226589 771633877648971340209971)
            ·
              refine ⟨1157450816473457010314957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771633877648971340209971 1157450816473457010314957)
              ·
                refine ⟨434044056177546378868109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1157450816473457010314957 434044056177546378868109)
                ·
                  refine ⟨162766521066579892075541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434044056177546378868109 162766521066579892075541)
                  ·
                    rfl

theorem cell21_713220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_713220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713220 prefixEnd_713220 := by exact prefixLift 713220
  have htrace : WordTrace (prefixWord ++ tailWord_713220) baseStart_713220 baseEnd_713220 := by
    simpa [prefixWord, tailWord_713220, baseEnd_713220] using wordTrace_append hprefix tailTrace_713220
  have hstable : (prefixWord ++ tailWord_713220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713220).length < 2 ^ (prefixWord ++ tailWord_713220).sum := by decide
  have hdescent : baseEnd_713220 < baseStart_713220 := by decide
  rcases family_descends (prefixWord ++ tailWord_713220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713293 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 4]
def baseStart_713293 : Nat := 118140960795 + 713293 * 2 ^ 59
def prefixEnd_713293 : Nat := 4983230072969 + 3 ^ 40 * 713293 * 2
def baseEnd_713293 : Nat := 162783180661147987358725

theorem tailTrace_713293 : CollatzResearch.WordTrace tailWord_713293 prefixEnd_713293 162783180661147987358725 := by
  unfold tailWord_713293
  simp only [CollatzResearch.WordTrace]
  refine ⟨26015933004868756590864533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17343955336579171060576355 26015933004868756590864533)
  ·
    refine ⟨1219496859603222965196775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26015933004868756590864533 1219496859603222965196775)
    ·
      refine ⟨1829245289404834447795163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1219496859603222965196775 1829245289404834447795163)
      ·
        refine ⟨2743867934107251671692745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829245289404834447795163 2743867934107251671692745)
        ·
          refine ⟨2057900950580438753769559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2743867934107251671692745 2057900950580438753769559)
          ·
            refine ⟨3086851425870658130654339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057900950580438753769559 3086851425870658130654339)
            ·
              refine ⟨4630277138805987195981509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086851425870658130654339 4630277138805987195981509)
              ·
                refine ⟨868176963526122599246533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4630277138805987195981509 868176963526122599246533)
                ·
                  refine ⟨162783180661147987358725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868176963526122599246533 162783180661147987358725)
                  ·
                    rfl

theorem cell21_713293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_713293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713293 prefixEnd_713293 := by exact prefixLift 713293
  have htrace : WordTrace (prefixWord ++ tailWord_713293) baseStart_713293 baseEnd_713293 := by
    simpa [prefixWord, tailWord_713293, baseEnd_713293] using wordTrace_append hprefix tailTrace_713293
  have hstable : (prefixWord ++ tailWord_713293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713293).length < 2 ^ (prefixWord ++ tailWord_713293).sum := by decide
  have hdescent : baseEnd_713293 < baseStart_713293 := by decide
  rcases family_descends (prefixWord ++ tailWord_713293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713487 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 4]
def baseStart_713487 : Nat := 118140960795 + 713487 * 2 ^ 59
def prefixEnd_713487 : Nat := 4983230072969 + 3 ^ 40 * 713487 * 2
def baseEnd_713487 : Nat := 162827454104246761124995

theorem tailTrace_713487 : CollatzResearch.WordTrace tailWord_713487 prefixEnd_713487 162827454104246761124995 := by
  unfold tailWord_713487
  simp only [CollatzResearch.WordTrace]
  refine ⟨26023008766165927723426715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17348672510777285148951143 26023008766165927723426715)
  ·
    refine ⟨39034513149248891585140073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26023008766165927723426715 39034513149248891585140073)
    ·
      refine ⟨29275884861936668688855055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39034513149248891585140073 29275884861936668688855055)
      ·
        refine ⟨43913827292905003033282583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29275884861936668688855055 43913827292905003033282583)
        ·
          refine ⟨65870740939357504549923875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43913827292905003033282583 65870740939357504549923875)
          ·
            refine ⟨98806111409036256824885813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65870740939357504549923875 98806111409036256824885813)
            ·
              refine ⟨9263072944597149077333045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98806111409036256824885813 9263072944597149077333045)
              ·
                refine ⟨868413088555982725999973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9263072944597149077333045 868413088555982725999973)
                ·
                  refine ⟨162827454104246761124995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 868413088555982725999973 162827454104246761124995)
                  ·
                    rfl

theorem cell21_713487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 4].length) (baseStart_713487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713487 prefixEnd_713487 := by exact prefixLift 713487
  have htrace : WordTrace (prefixWord ++ tailWord_713487) baseStart_713487 baseEnd_713487 := by
    simpa [prefixWord, tailWord_713487, baseEnd_713487] using wordTrace_append hprefix tailTrace_713487
  have hstable : (prefixWord ++ tailWord_713487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713487).length < 2 ^ (prefixWord ++ tailWord_713487).sum := by decide
  have hdescent : baseEnd_713487 < baseStart_713487 := by decide
  rcases family_descends (prefixWord ++ tailWord_713487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713625 : List Nat := [1, 2, 1, 2, 1, 3, 1, 7, 3]
def baseStart_713625 : Nat := 118140960795 + 713625 * 2 ^ 59
def prefixEnd_713625 : Nat := 4983230072969 + 3 ^ 40 * 713625 * 2
def baseEnd_713625 : Nat := 162858947584389187824713

theorem tailTrace_713625 : CollatzResearch.WordTrace tailWord_713625 prefixEnd_713625 162858947584389187824713 := by
  unfold tailWord_713625
  simp only [CollatzResearch.WordTrace]
  refine ⟨26028042039665977291950329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17352028026443984861300219 26028042039665977291950329)
  ·
    refine ⟨19521031529749482968962747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26028042039665977291950329 19521031529749482968962747)
    ·
      refine ⟨29281547294624224453444121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19521031529749482968962747 29281547294624224453444121)
      ·
        refine ⟨21961160470968168340083091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29281547294624224453444121 21961160470968168340083091)
        ·
          refine ⟨32941740706452252510124637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21961160470968168340083091 32941740706452252510124637)
          ·
            refine ⟨12353152764919594691296739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32941740706452252510124637 12353152764919594691296739)
            ·
              refine ⟨18529729147379392036945109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12353152764919594691296739 18529729147379392036945109)
              ·
                refine ⟨434290526891704500865901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18529729147379392036945109 434290526891704500865901)
                ·
                  refine ⟨162858947584389187824713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434290526891704500865901 162858947584389187824713)
                  ·
                    rfl

theorem cell21_713625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_713625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713625 prefixEnd_713625 := by exact prefixLift 713625
  have htrace : WordTrace (prefixWord ++ tailWord_713625) baseStart_713625 baseEnd_713625 := by
    simpa [prefixWord, tailWord_713625, baseEnd_713625] using wordTrace_append hprefix tailTrace_713625
  have hstable : (prefixWord ++ tailWord_713625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713625).length < 2 ^ (prefixWord ++ tailWord_713625).sum := by decide
  have hdescent : baseEnd_713625 < baseStart_713625 := by decide
  rcases family_descends (prefixWord ++ tailWord_713625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713645 : List Nat := [1, 5, 2, 3, 2, 1, 1, 6]
def baseStart_713645 : Nat := 118140960795 + 713645 * 2 ^ 59
def prefixEnd_713645 : Nat := 4983230072969 + 3 ^ 40 * 713645 * 2
def baseEnd_713645 : Nat := 54287837285624532497113

theorem tailTrace_713645 : CollatzResearch.WordTrace tailWord_713645 prefixEnd_713645 54287837285624532497113 := by
  unfold tailWord_713645
  simp only [CollatzResearch.WordTrace]
  refine ⟨26028771499593520707678389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17352514333062347138452259 26028771499593520707678389)
  ·
    refine ⟨2440197328086892566344849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26028771499593520707678389 2440197328086892566344849)
    ·
      refine ⟨1830147996065169424758637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2440197328086892566344849 1830147996065169424758637)
      ·
        refine ⟨686305498524438534284489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1830147996065169424758637 686305498524438534284489)
        ·
          refine ⟨514729123893328900713367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686305498524438534284489 514729123893328900713367)
          ·
            refine ⟨772093685839993351070051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514729123893328900713367 772093685839993351070051)
            ·
              refine ⟨1158140528759990026605077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772093685839993351070051 1158140528759990026605077)
              ·
                refine ⟨54287837285624532497113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1158140528759990026605077 54287837285624532497113)
                ·
                  rfl

theorem cell21_713645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 6].length) (baseStart_713645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713645 prefixEnd_713645 := by exact prefixLift 713645
  have htrace : WordTrace (prefixWord ++ tailWord_713645) baseStart_713645 baseEnd_713645 := by
    simpa [prefixWord, tailWord_713645, baseEnd_713645] using wordTrace_append hprefix tailTrace_713645
  have hstable : (prefixWord ++ tailWord_713645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713645).length < 2 ^ (prefixWord ++ tailWord_713645).sum := by decide
  have hdescent : baseEnd_713645 < baseStart_713645 := by decide
  rcases family_descends (prefixWord ++ tailWord_713645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713836 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_713836 : Nat := 118140960795 + 713836 * 2 ^ 59
def prefixEnd_713836 : Nat := 4983230072969 + 3 ^ 40 * 713836 * 2
def baseEnd_713836 : Nat := 162907100659099709807615

theorem tailTrace_713836 : CollatzResearch.WordTrace tailWord_713836 prefixEnd_713836 162907100659099709807615 := by
  unfold tailWord_713836
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017868920950780163940681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17357158561267706885254241 13017868920950780163940681)
  ·
    refine ⟨9763401690713085122955511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13017868920950780163940681 9763401690713085122955511)
    ·
      refine ⟨14645102536069627684433267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9763401690713085122955511 14645102536069627684433267)
      ·
        refine ⟨21967653804104441526649901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14645102536069627684433267 21967653804104441526649901)
        ·
          refine ⟨8237870176539165572493713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21967653804104441526649901 8237870176539165572493713)
          ·
            refine ⟨6178402632404374179370285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8237870176539165572493713 6178402632404374179370285)
            ·
              refine ⟨2316900987151640317263857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6178402632404374179370285 2316900987151640317263857)
              ·
                refine ⟨1737675740363730237947893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316900987151640317263857 1737675740363730237947893)
                ·
                  refine ⟨162907100659099709807615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1737675740363730237947893 162907100659099709807615)
                  ·
                    rfl

theorem cell21_713836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_713836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713836 prefixEnd_713836 := by exact prefixLift 713836
  have htrace : WordTrace (prefixWord ++ tailWord_713836) baseStart_713836 baseEnd_713836 := by
    simpa [prefixWord, tailWord_713836, baseEnd_713836] using wordTrace_append hprefix tailTrace_713836
  have hstable : (prefixWord ++ tailWord_713836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713836).length < 2 ^ (prefixWord ++ tailWord_713836).sum := by decide
  have hdescent : baseEnd_713836 < baseStart_713836 := by decide
  rcases family_descends (prefixWord ++ tailWord_713836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713870 : List Nat := [4, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_713870 : Nat := 118140960795 + 713870 * 2 ^ 59
def prefixEnd_713870 : Nat := 4983230072969 + 3 ^ 40 * 713870 * 2
def baseEnd_713870 : Nat := 162914859922323206240879

theorem tailTrace_713870 : CollatzResearch.WordTrace tailWord_713870 prefixEnd_713870 162914859922323206240879 := by
  unfold tailWord_713870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254622240472298016827383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17357985282518922756412709 3254622240472298016827383)
  ·
    refine ⟨4881933360708447025241075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254622240472298016827383 4881933360708447025241075)
    ·
      refine ⟨7322900041062670537861613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4881933360708447025241075 7322900041062670537861613)
      ·
        refine ⟨2746087515398501451698105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7322900041062670537861613 2746087515398501451698105)
        ·
          refine ⟨2059565636548876088773579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2746087515398501451698105 2059565636548876088773579)
          ·
            refine ⟨3089348454823314133160369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059565636548876088773579 3089348454823314133160369)
            ·
              refine ⟨2317011341117485599870277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089348454823314133160369 2317011341117485599870277)
              ·
                refine ⟨434439626459528549975677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2317011341117485599870277 434439626459528549975677)
                ·
                  refine ⟨162914859922323206240879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434439626459528549975677 162914859922323206240879)
                  ·
                    rfl

theorem cell21_713870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_713870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713870 prefixEnd_713870 := by exact prefixLift 713870
  have htrace : WordTrace (prefixWord ++ tailWord_713870) baseStart_713870 baseEnd_713870 := by
    simpa [prefixWord, tailWord_713870, baseEnd_713870] using wordTrace_append hprefix tailTrace_713870
  have hstable : (prefixWord ++ tailWord_713870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713870).length < 2 ^ (prefixWord ++ tailWord_713870).sum := by decide
  have hdescent : baseEnd_713870 < baseStart_713870 := by decide
  rcases family_descends (prefixWord ++ tailWord_713870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713980 : List Nat := [2, 2, 2, 1, 6, 1, 2, 2, 3]
def baseStart_713980 : Nat := 118140960795 + 713980 * 2 ^ 59
def prefixEnd_713980 : Nat := 4983230072969 + 3 ^ 40 * 713980 * 2
def baseEnd_713980 : Nat := 162939963420987459407321

theorem tailTrace_713980 : CollatzResearch.WordTrace tailWord_713980 prefixEnd_713980 162939963420987459407321 := by
  unfold tailWord_713980
  simp only [CollatzResearch.WordTrace]
  refine ⟨13020494976689936460561697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17360659968919915280748929 13020494976689936460561697)
  ·
    refine ⟨9765371232517452345421273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13020494976689936460561697 9765371232517452345421273)
    ·
      refine ⟨7324028424388089259065955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9765371232517452345421273 7324028424388089259065955)
      ·
        refine ⟨10986042636582133888598933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7324028424388089259065955 10986042636582133888598933)
        ·
          refine ⟨514970748589787526028075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10986042636582133888598933 514970748589787526028075)
          ·
            refine ⟨772456122884681289042113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514970748589787526028075 772456122884681289042113)
            ·
              refine ⟨579342092163510966781585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772456122884681289042113 579342092163510966781585)
              ·
                refine ⟨434506569122633225086189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579342092163510966781585 434506569122633225086189)
                ·
                  refine ⟨162939963420987459407321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434506569122633225086189 162939963420987459407321)
                  ·
                    rfl

theorem cell21_713980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_713980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_713980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_713980 prefixEnd_713980 := by exact prefixLift 713980
  have htrace : WordTrace (prefixWord ++ tailWord_713980) baseStart_713980 baseEnd_713980 := by
    simpa [prefixWord, tailWord_713980, baseEnd_713980] using wordTrace_append hprefix tailTrace_713980
  have hstable : (prefixWord ++ tailWord_713980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713980).length < 2 ^ (prefixWord ++ tailWord_713980).sum := by decide
  have hdescent : baseEnd_713980 < baseStart_713980 := by decide
  rcases family_descends (prefixWord ++ tailWord_713980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714033 : List Nat := [1, 2, 2, 3, 3, 2, 8]
def baseStart_714033 : Nat := 118140960795 + 714033 * 2 ^ 59
def prefixEnd_714033 : Nat := 4983230072969 + 3 ^ 40 * 714033 * 2
def baseEnd_714033 : Nat := 18105784304785682780431

theorem tailTrace_714033 : CollatzResearch.WordTrace tailWord_714033 prefixEnd_714033 18105784304785682780431 := by
  unfold tailWord_714033
  simp only [CollatzResearch.WordTrace]
  refine ⟨26042923022187862972802753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17361948681458575315201835 26042923022187862972802753)
  ·
    refine ⟨19532192266640897229602065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26042923022187862972802753 19532192266640897229602065)
    ·
      refine ⟨14649144199980672922201549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19532192266640897229602065 14649144199980672922201549)
      ·
        refine ⟨5493429074992752345825581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14649144199980672922201549 5493429074992752345825581)
        ·
          refine ⟨2060035903122282129684593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5493429074992752345825581 2060035903122282129684593)
          ·
            refine ⟨1545026927341711597263445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060035903122282129684593 1545026927341711597263445)
            ·
              refine ⟨18105784304785682780431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1545026927341711597263445 18105784304785682780431)
              ·
                rfl

theorem cell21_714033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 8].length) (baseStart_714033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714033 prefixEnd_714033 := by exact prefixLift 714033
  have htrace : WordTrace (prefixWord ++ tailWord_714033) baseStart_714033 baseEnd_714033 := by
    simpa [prefixWord, tailWord_714033, baseEnd_714033] using wordTrace_append hprefix tailTrace_714033
  have hstable : (prefixWord ++ tailWord_714033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714033).length < 2 ^ (prefixWord ++ tailWord_714033).sum := by decide
  have hdescent : baseEnd_714033 < baseStart_714033 := by decide
  rcases family_descends (prefixWord ++ tailWord_714033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714098 : List Nat := [3, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_714098 : Nat := 118140960795 + 714098 * 2 ^ 59
def prefixEnd_714098 : Nat := 4983230072969 + 3 ^ 40 * 714098 * 2
def baseEnd_714098 : Nat := 162966892628645476440413

theorem tailTrace_714098 : CollatzResearch.WordTrace tailWord_714098 prefixEnd_714098 162966892628645476440413 := by
  unfold tailWord_714098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511323441738094768479737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17363529177968252715945965 6511323441738094768479737)
  ·
    refine ⟨4883492581303571076359803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6511323441738094768479737 4883492581303571076359803)
    ·
      refine ⟨7325238871955356614539705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883492581303571076359803 7325238871955356614539705)
      ·
        refine ⟨5493929153966517460904779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7325238871955356614539705 5493929153966517460904779)
        ·
          refine ⟨8240893730949776191357169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493929153966517460904779 8240893730949776191357169)
          ·
            refine ⟨6180670298212332143517877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8240893730949776191357169 6180670298212332143517877)
            ·
              refine ⟨579437840457406138454801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6180670298212332143517877 579437840457406138454801)
              ·
                refine ⟨434578380343054603841101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579437840457406138454801 434578380343054603841101)
                ·
                  refine ⟨162966892628645476440413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434578380343054603841101 162966892628645476440413)
                  ·
                    rfl

theorem cell21_714098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_714098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714098 prefixEnd_714098 := by exact prefixLift 714098
  have htrace : WordTrace (prefixWord ++ tailWord_714098) baseStart_714098 baseEnd_714098 := by
    simpa [prefixWord, tailWord_714098, baseEnd_714098] using wordTrace_append hprefix tailTrace_714098
  have hstable : (prefixWord ++ tailWord_714098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714098).length < 2 ^ (prefixWord ++ tailWord_714098).sum := by decide
  have hdescent : baseEnd_714098 < baseStart_714098 := by decide
  rcases family_descends (prefixWord ++ tailWord_714098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714109 : List Nat := [1, 4, 1, 1, 2, 2, 4, 6]
def baseStart_714109 : Nat := 118140960795 + 714109 * 2 ^ 59
def prefixEnd_714109 : Nat := 4983230072969 + 3 ^ 40 * 714109 * 2
def baseEnd_714109 : Nat := 54323134326170633919019

theorem tailTrace_714109 : CollatzResearch.WordTrace tailWord_714109 prefixEnd_714109 54323134326170633919019 := by
  unfold tailWord_714109
  simp only [CollatzResearch.WordTrace]
  refine ⟨26045694969912527952569381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17363796646608351968379587 26045694969912527952569381)
  ·
    refine ⟨4883567806858598991106759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26045694969912527952569381 4883567806858598991106759)
    ·
      refine ⟨7325351710287898486660139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883567806858598991106759 7325351710287898486660139)
      ·
        refine ⟨10988027565431847729990209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7325351710287898486660139 10988027565431847729990209)
        ·
          refine ⟨8241020674073885797492657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10988027565431847729990209 8241020674073885797492657)
          ·
            refine ⟨6180765505555414348119493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8241020674073885797492657 6180765505555414348119493)
            ·
              refine ⟨1158893532291640190272405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6180765505555414348119493 1158893532291640190272405)
              ·
                refine ⟨54323134326170633919019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1158893532291640190272405 54323134326170633919019)
                ·
                  rfl

theorem cell21_714109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 6].length) (baseStart_714109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714109 prefixEnd_714109 := by exact prefixLift 714109
  have htrace : WordTrace (prefixWord ++ tailWord_714109) baseStart_714109 baseEnd_714109 := by
    simpa [prefixWord, tailWord_714109, baseEnd_714109] using wordTrace_append hprefix tailTrace_714109
  have hstable : (prefixWord ++ tailWord_714109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714109).length < 2 ^ (prefixWord ++ tailWord_714109).sum := by decide
  have hdescent : baseEnd_714109 < baseStart_714109 := by decide
  rcases family_descends (prefixWord ++ tailWord_714109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714123 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 7]
def baseStart_714123 : Nat := 118140960795 + 714123 * 2 ^ 59
def prefixEnd_714123 : Nat := 4983230072969 + 3 ^ 40 * 714123 * 2
def baseEnd_714123 : Nat := 162972597969250988523695

theorem tailTrace_714123 : CollatzResearch.WordTrace tailWord_714123 prefixEnd_714123 162972597969250988523695 := by
  unfold tailWord_714123
  simp only [CollatzResearch.WordTrace]
  refine ⟨26046205591861808343579023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17364137061241205562386015 26046205591861808343579023)
  ·
    refine ⟨39069308387792712515368535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26046205591861808343579023 39069308387792712515368535)
    ·
      refine ⟨58603962581689068773052803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39069308387792712515368535 58603962581689068773052803)
      ·
        refine ⟨87905943872533603159579205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58603962581689068773052803 87905943872533603159579205)
        ·
          refine ⟨16482364476100050592421101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87905943872533603159579205 16482364476100050592421101)
          ·
            refine ⟨6180886678537518972157913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16482364476100050592421101 6180886678537518972157913)
            ·
              refine ⟨4635665008903139229118435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6180886678537518972157913 4635665008903139229118435)
              ·
                refine ⟨6953497513354708843677653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635665008903139229118435 6953497513354708843677653)
                ·
                  refine ⟨162972597969250988523695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6953497513354708843677653 162972597969250988523695)
                  ·
                    rfl

theorem cell21_714123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_714123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714123 prefixEnd_714123 := by exact prefixLift 714123
  have htrace : WordTrace (prefixWord ++ tailWord_714123) baseStart_714123 baseEnd_714123 := by
    simpa [prefixWord, tailWord_714123, baseEnd_714123] using wordTrace_append hprefix tailTrace_714123
  have hstable : (prefixWord ++ tailWord_714123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714123).length < 2 ^ (prefixWord ++ tailWord_714123).sum := by decide
  have hdescent : baseEnd_714123 < baseStart_714123 := by decide
  rcases family_descends (prefixWord ++ tailWord_714123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714216 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_714216 : Nat := 118140960795 + 714216 * 2 ^ 59
def prefixEnd_714216 : Nat := 4983230072969 + 3 ^ 40 * 714216 * 2
def baseEnd_714216 : Nat := 162993821836303493473505

theorem tailTrace_714216 : CollatzResearch.WordTrace tailWord_714216 prefixEnd_714216 162993821836303493473505 := by
  unfold tailWord_714216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13024798790262442613357251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17366398387016590151143001 13024798790262442613357251)
  ·
    refine ⟨19537198185393663920035877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13024798790262442613357251 19537198185393663920035877)
    ·
      refine ⟨3663224659761311985006727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19537198185393663920035877 3663224659761311985006727)
      ·
        refine ⟨5494836989641967977510091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663224659761311985006727 5494836989641967977510091)
        ·
          refine ⟨8242255484462951966265137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5494836989641967977510091 8242255484462951966265137)
          ·
            refine ⟨6181691613347213974698853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8242255484462951966265137 6181691613347213974698853)
            ·
              refine ⟨1159067177502602620256035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6181691613347213974698853 1159067177502602620256035)
              ·
                refine ⟨1738600766253903930384053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159067177502602620256035 1738600766253903930384053)
                ·
                  refine ⟨162993821836303493473505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1738600766253903930384053 162993821836303493473505)
                  ·
                    rfl

theorem cell21_714216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_714216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714216 prefixEnd_714216 := by exact prefixLift 714216
  have htrace : WordTrace (prefixWord ++ tailWord_714216) baseStart_714216 baseEnd_714216 := by
    simpa [prefixWord, tailWord_714216, baseEnd_714216] using wordTrace_append hprefix tailTrace_714216
  have hstable : (prefixWord ++ tailWord_714216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714216).length < 2 ^ (prefixWord ++ tailWord_714216).sum := by decide
  have hdescent : baseEnd_714216 < baseStart_714216 := by decide
  rcases family_descends (prefixWord ++ tailWord_714216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714250 : List Nat := [3, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_714250 : Nat := 118140960795 + 714250 * 2 ^ 59
def prefixEnd_714250 : Nat := 4983230072969 + 3 ^ 40 * 714250 * 2
def baseEnd_714250 : Nat := 163001581099526989906769

theorem tailTrace_714250 : CollatzResearch.WordTrace tailWord_714250 prefixEnd_714250 163001581099526989906769 := by
  unfold tailWord_714250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6512709415600427258363051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17367225108267806022301469 6512709415600427258363051)
  ·
    refine ⟨9769064123400640887544577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6512709415600427258363051 9769064123400640887544577)
    ·
      refine ⟨7326798092550480665658433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9769064123400640887544577 7326798092550480665658433)
      ·
        refine ⟨5495098569412860499243825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7326798092550480665658433 5495098569412860499243825)
        ·
          refine ⟨4121323927059645374432869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5495098569412860499243825 4121323927059645374432869)
          ·
            refine ⟨772748236323683507706163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4121323927059645374432869 772748236323683507706163)
            ·
              refine ⟨1159122354485525261559245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772748236323683507706163 1159122354485525261559245)
              ·
                refine ⟨434670882932071973084717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1159122354485525261559245 434670882932071973084717)
                ·
                  refine ⟨163001581099526989906769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434670882932071973084717 163001581099526989906769)
                  ·
                    rfl

theorem cell21_714250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_714250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714250 prefixEnd_714250 := by exact prefixLift 714250
  have htrace : WordTrace (prefixWord ++ tailWord_714250) baseStart_714250 baseEnd_714250 := by
    simpa [prefixWord, tailWord_714250, baseEnd_714250] using wordTrace_append hprefix tailTrace_714250
  have hstable : (prefixWord ++ tailWord_714250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714250).length < 2 ^ (prefixWord ++ tailWord_714250).sum := by decide
  have hdescent : baseEnd_714250 < baseStart_714250 := by decide
  rcases family_descends (prefixWord ++ tailWord_714250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714261 : List Nat := [1, 3, 2, 1, 3, 4, 7]
def baseStart_714261 : Nat := 118140960795 + 714261 * 2 ^ 59
def prefixEnd_714261 : Nat := 4983230072969 + 3 ^ 40 * 714261 * 2
def baseEnd_714261 : Nat := 18111565716599268358157

theorem tailTrace_714261 : CollatzResearch.WordTrace tailWord_714261 prefixEnd_714261 18111565716599268358157 := by
  unfold tailWord_714261
  simp only [CollatzResearch.WordTrace]
  refine ⟨26051238865361857912102637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17367492576907905274735091 26051238865361857912102637)
  ·
    refine ⟨9769214574510696717038489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26051238865361857912102637 9769214574510696717038489)
    ·
      refine ⟨7326910930883022537778867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9769214574510696717038489 7326910930883022537778867)
      ·
        refine ⟨10990366396324533806668301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7326910930883022537778867 10990366396324533806668301)
        ·
          refine ⟨4121387398621700177500613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10990366396324533806668301 4121387398621700177500613)
          ·
            refine ⟨772760137241568783281365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4121387398621700177500613 772760137241568783281365)
            ·
              refine ⟨18111565716599268358157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 772760137241568783281365 18111565716599268358157)
              ·
                rfl

theorem cell21_714261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 7].length) (baseStart_714261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714261 prefixEnd_714261 := by exact prefixLift 714261
  have htrace : WordTrace (prefixWord ++ tailWord_714261) baseStart_714261 baseEnd_714261 := by
    simpa [prefixWord, tailWord_714261, baseEnd_714261] using wordTrace_append hprefix tailTrace_714261
  have hstable : (prefixWord ++ tailWord_714261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714261).length < 2 ^ (prefixWord ++ tailWord_714261).sum := by decide
  have hdescent : baseEnd_714261 < baseStart_714261 := by decide
  rcases family_descends (prefixWord ++ tailWord_714261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714354 : List Nat := [3, 2, 1, 2, 3, 2, 3, 5]
def baseStart_714354 : Nat := 118140960795 + 714354 * 2 ^ 59
def prefixEnd_714354 : Nat := 4983230072969 + 3 ^ 40 * 714354 * 2
def baseEnd_714354 : Nat := 54341771772148640057741

theorem tailTrace_714354 : CollatzResearch.WordTrace tailWord_714354 prefixEnd_714354 54341771772148640057741 := by
  unfold tailWord_714354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513657713506233698809529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17369753902683289863492077 6513657713506233698809529)
  ·
    refine ⟨4885243285129675274107147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6513657713506233698809529 4885243285129675274107147)
    ·
      refine ⟨7327864927694512911160721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4885243285129675274107147 7327864927694512911160721)
      ·
        refine ⟨5495898695770884683370541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7327864927694512911160721 5495898695770884683370541)
        ·
          refine ⟨2060962010914081756263953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5495898695770884683370541 2060962010914081756263953)
          ·
            refine ⟨1545721508185561317197965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060962010914081756263953 1545721508185561317197965)
            ·
              refine ⟨579645565569585493949237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1545721508185561317197965 579645565569585493949237)
              ·
                refine ⟨54341771772148640057741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 579645565569585493949237 54341771772148640057741)
                ·
                  rfl

theorem cell21_714354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_714354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714354 prefixEnd_714354 := by exact prefixLift 714354
  have htrace : WordTrace (prefixWord ++ tailWord_714354) baseStart_714354 baseEnd_714354 := by
    simpa [prefixWord, tailWord_714354, baseEnd_714354] using wordTrace_append hprefix tailTrace_714354
  have hstable : (prefixWord ++ tailWord_714354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714354).length < 2 ^ (prefixWord ++ tailWord_714354).sum := by decide
  have hdescent : baseEnd_714354 < baseStart_714354 := by decide
  rcases family_descends (prefixWord ++ tailWord_714354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714413 : List Nat := [1, 5, 2, 1, 1, 1, 3, 7]
def baseStart_714413 : Nat := 118140960795 + 714413 * 2 ^ 59
def prefixEnd_714413 : Nat := 4983230072969 + 3 ^ 40 * 714413 * 2
def baseEnd_714413 : Nat := 54346259973424976229923

theorem tailTrace_714413 : CollatzResearch.WordTrace tailWord_714413 prefixEnd_714413 54346259973424976229923 := by
  unfold tailWord_714413
  simp only [CollatzResearch.WordTrace]
  refine ⟨26056782760811187871635893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17371188507207458581090595 26056782760811187871635893)
  ·
    refine ⟨2442823383826048862965865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26056782760811187871635893 2442823383826048862965865)
    ·
      refine ⟨1832117537869536647224399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2442823383826048862965865 1832117537869536647224399)
      ·
        refine ⟨2748176306804304970836599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832117537869536647224399 2748176306804304970836599)
        ·
          refine ⟨4122264460206457456254899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2748176306804304970836599 4122264460206457456254899)
          ·
            refine ⟨6183396690309686184382349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122264460206457456254899 6183396690309686184382349)
            ·
              refine ⟨2318773758866132319143381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6183396690309686184382349 2318773758866132319143381)
              ·
                refine ⟨54346259973424976229923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2318773758866132319143381 54346259973424976229923)
                ·
                  rfl

theorem cell21_714413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 7].length) (baseStart_714413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714413 prefixEnd_714413 := by exact prefixLift 714413
  have htrace : WordTrace (prefixWord ++ tailWord_714413) baseStart_714413 baseEnd_714413 := by
    simpa [prefixWord, tailWord_714413, baseEnd_714413] using wordTrace_append hprefix tailTrace_714413
  have hstable : (prefixWord ++ tailWord_714413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714413).length < 2 ^ (prefixWord ++ tailWord_714413).sum := by decide
  have hdescent : baseEnd_714413 < baseStart_714413 := by decide
  rcases family_descends (prefixWord ++ tailWord_714413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714593 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 8]
def baseStart_714593 : Nat := 118140960795 + 714593 * 2 ^ 59
def prefixEnd_714593 : Nat := 4983230072969 + 3 ^ 40 * 714593 * 2
def baseEnd_714593 : Nat := 163079858372634615689401

theorem tailTrace_714593 : CollatzResearch.WordTrace tailWord_714593 prefixEnd_714593 163079858372634615689401 := by
  unfold tailWord_714593
  simp only [CollatzResearch.WordTrace]
  refine ⟨26063347900159078613188433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17375565266772719075458955 26063347900159078613188433)
  ·
    refine ⟨19547510925119308959891325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26063347900159078613188433 19547510925119308959891325)
    ·
      refine ⟨7330316596919740859959247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19547510925119308959891325 7330316596919740859959247)
      ·
        refine ⟨10995474895379611289938871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7330316596919740859959247 10995474895379611289938871)
        ·
          refine ⟨16493212343069416934908307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10995474895379611289938871 16493212343069416934908307)
          ·
            refine ⟨24739818514604125402362461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16493212343069416934908307 24739818514604125402362461)
            ·
              refine ⟨9277431942976547025885923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24739818514604125402362461 9277431942976547025885923)
              ·
                refine ⟨13916147914464820538828885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9277431942976547025885923 13916147914464820538828885)
                ·
                  refine ⟨163079858372634615689401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13916147914464820538828885 163079858372634615689401)
                  ·
                    rfl

theorem cell21_714593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_714593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714593 prefixEnd_714593 := by exact prefixLift 714593
  have htrace : WordTrace (prefixWord ++ tailWord_714593) baseStart_714593 baseEnd_714593 := by
    simpa [prefixWord, tailWord_714593, baseEnd_714593] using wordTrace_append hprefix tailTrace_714593
  have hstable : (prefixWord ++ tailWord_714593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714593).length < 2 ^ (prefixWord ++ tailWord_714593).sum := by decide
  have hdescent : baseEnd_714593 < baseStart_714593 := by decide
  rcases family_descends (prefixWord ++ tailWord_714593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714610 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_714610 : Nat := 118140960795 + 714610 * 2 ^ 59
def prefixEnd_714610 : Nat := 4983230072969 + 3 ^ 40 * 714610 * 2
def baseEnd_714610 : Nat := 163083738004246363906033

theorem tailTrace_714610 : CollatzResearch.WordTrace tailWord_714610 prefixEnd_714610 163083738004246363906033 := by
  unfold tailWord_714610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515991985274372629139321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17375978627398327011038189 6515991985274372629139321)
  ·
    refine ⟨4886993988955779471854491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6515991985274372629139321 4886993988955779471854491)
    ·
      refine ⟨7330490983433669207781737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4886993988955779471854491 7330490983433669207781737)
      ·
        refine ⟨5497868237575251905836303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7330490983433669207781737 5497868237575251905836303)
        ·
          refine ⟨8246802356362877858754455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497868237575251905836303 8246802356362877858754455)
          ·
            refine ⟨12370203534544316788131683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8246802356362877858754455 12370203534544316788131683)
            ·
              refine ⟨18555305301816475182197525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12370203534544316788131683 18555305301816475182197525)
              ·
                refine ⟨869779936022647274165509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18555305301816475182197525 869779936022647274165509)
                ·
                  refine ⟨163083738004246363906033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 869779936022647274165509 163083738004246363906033)
                  ·
                    rfl

theorem cell21_714610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_714610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714610 prefixEnd_714610 := by exact prefixLift 714610
  have htrace : WordTrace (prefixWord ++ tailWord_714610) baseStart_714610 baseEnd_714610 := by
    simpa [prefixWord, tailWord_714610, baseEnd_714610] using wordTrace_append hprefix tailTrace_714610
  have hstable : (prefixWord ++ tailWord_714610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714610).length < 2 ^ (prefixWord ++ tailWord_714610).sum := by decide
  have hdescent : baseEnd_714610 < baseStart_714610 := by decide
  rcases family_descends (prefixWord ++ tailWord_714610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714624 : List Nat := [2, 1, 1, 2, 1, 2, 6, 6]
def baseStart_714624 : Nat := 118140960795 + 714624 * 2 ^ 59
def prefixEnd_714624 : Nat := 4983230072969 + 3 ^ 40 * 714624 * 2
def baseEnd_714624 : Nat := 54362310998328483557557

theorem tailTrace_714624 : CollatzResearch.WordTrace tailWord_714624 prefixEnd_714624 54362310998328483557557 := by
  unfold tailWord_714624
  simp only [CollatzResearch.WordTrace]
  refine ⟨13032239281523385453783463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17376319042031180605044617 13032239281523385453783463)
  ·
    refine ⟨19548358922285078180675195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13032239281523385453783463 19548358922285078180675195)
    ·
      refine ⟨29322538383427617271012793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19548358922285078180675195 29322538383427617271012793)
      ·
        refine ⟨21991903787570712953259595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29322538383427617271012793 21991903787570712953259595)
        ·
          refine ⟨32987855681356069429889393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21991903787570712953259595 32987855681356069429889393)
          ·
            refine ⟨24740891761017052072417045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32987855681356069429889393 24740891761017052072417045)
            ·
              refine ⟨1159729301297674315894549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24740891761017052072417045 1159729301297674315894549)
              ·
                refine ⟨54362310998328483557557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1159729301297674315894549 54362310998328483557557)
                ·
                  rfl

theorem cell21_714624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_714624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714624 prefixEnd_714624 := by exact prefixLift 714624
  have htrace : WordTrace (prefixWord ++ tailWord_714624) baseStart_714624 baseEnd_714624 := by
    simpa [prefixWord, tailWord_714624, baseEnd_714624] using wordTrace_append hprefix tailTrace_714624
  have hstable : (prefixWord ++ tailWord_714624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714624).length < 2 ^ (prefixWord ++ tailWord_714624).sum := by decide
  have hdescent : baseEnd_714624 < baseStart_714624 := by decide
  rcases family_descends (prefixWord ++ tailWord_714624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714627 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 4]
def baseStart_714627 : Nat := 118140960795 + 714627 * 2 ^ 59
def prefixEnd_714627 : Nat := 4983230072969 + 3 ^ 40 * 714627 * 2
def baseEnd_714627 : Nat := 163087617635858112122665

theorem tailTrace_714627 : CollatzResearch.WordTrace tailWord_714627 prefixEnd_714627 163087617635858112122665 := by
  unfold tailWord_714627
  simp only [CollatzResearch.WordTrace]
  refine ⟨26064587982035902419926135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17376391988023934946617423 26064587982035902419926135)
  ·
    refine ⟨39096881973053853629889203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26064587982035902419926135 39096881973053853629889203)
    ·
      refine ⟨58645322959580780444833805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39096881973053853629889203 58645322959580780444833805)
      ·
        refine ⟨21991996109842792666812677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58645322959580780444833805 21991996109842792666812677)
        ·
          refine ⟨4123499270595523625027377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21991996109842792666812677 4123499270595523625027377)
          ·
            refine ⟨3092624452946642718770533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4123499270595523625027377 3092624452946642718770533)
            ·
              refine ⟨579867084927495509769475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3092624452946642718770533 579867084927495509769475)
              ·
                refine ⟨869800627391243264654213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579867084927495509769475 869800627391243264654213)
                ·
                  refine ⟨163087617635858112122665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 869800627391243264654213 163087617635858112122665)
                  ·
                    rfl

theorem cell21_714627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 4].length) (baseStart_714627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714627 prefixEnd_714627 := by exact prefixLift 714627
  have htrace : WordTrace (prefixWord ++ tailWord_714627) baseStart_714627 baseEnd_714627 := by
    simpa [prefixWord, tailWord_714627, baseEnd_714627] using wordTrace_append hprefix tailTrace_714627
  have hstable : (prefixWord ++ tailWord_714627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714627).length < 2 ^ (prefixWord ++ tailWord_714627).sum := by decide
  have hdescent : baseEnd_714627 < baseStart_714627 := by decide
  rcases family_descends (prefixWord ++ tailWord_714627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714664 : List Nat := [2, 1, 6, 2, 1, 2, 2, 2, 3]
def baseStart_714664 : Nat := 118140960795 + 714664 * 2 ^ 59
def prefixEnd_714664 : Nat := 4983230072969 + 3 ^ 40 * 714664 * 2
def baseEnd_714664 : Nat := 163096061539954270005923

theorem tailTrace_714664 : CollatzResearch.WordTrace tailWord_714664 prefixEnd_714664 163096061539954270005923 := by
  unfold tailWord_714664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13032968741450928869511523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17377291655267905159348697 13032968741450928869511523)
  ·
    refine ⟨19549453112176393304267285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13032968741450928869511523 19549453112176393304267285)
    ·
      refine ⟨916380614633268436137529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19549453112176393304267285 916380614633268436137529)
      ·
        refine ⟨687285460974951327103147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 916380614633268436137529 687285460974951327103147)
        ·
          refine ⟨1030928191462426990654721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687285460974951327103147 1030928191462426990654721)
          ·
            refine ⟨773196143596820242991041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030928191462426990654721 773196143596820242991041)
            ·
              refine ⟨579897107697615182243281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773196143596820242991041 579897107697615182243281)
              ·
                refine ⟨434922830773211386682461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579897107697615182243281 434922830773211386682461)
                ·
                  refine ⟨163096061539954270005923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434922830773211386682461 163096061539954270005923)
                  ·
                    rfl

theorem cell21_714664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_714664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_714664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_714664 prefixEnd_714664 := by exact prefixLift 714664
  have htrace : WordTrace (prefixWord ++ tailWord_714664) baseStart_714664 baseEnd_714664 := by
    simpa [prefixWord, tailWord_714664, baseEnd_714664] using wordTrace_append hprefix tailTrace_714664
  have hstable : (prefixWord ++ tailWord_714664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714664).length < 2 ^ (prefixWord ++ tailWord_714664).sum := by decide
  have hdescent : baseEnd_714664 < baseStart_714664 := by decide
  rcases family_descends (prefixWord ++ tailWord_714664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
