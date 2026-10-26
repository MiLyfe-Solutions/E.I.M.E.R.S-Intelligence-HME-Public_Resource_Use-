import V185TrunkScan23Chunk1351

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8006616 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 1, 7]
def baseStart_8006616 : Nat := 118140960795 + 8006616 * 2 ^ 59
def prefixEnd_8006616 : Nat := 4983230072969 + 3 ^ 40 * 8006616 * 2
def baseEnd_8006616 : Nat := 1370414141326317103926083

theorem tailTrace_8006616 : CollatzResearch.WordTrace tailWord_8006616 prefixEnd_8006616 1370414141326317103926083 := by
  unfold tailWord_8006616
  simp only [CollatzResearch.WordTrace]
  refine ⟨146012638180702563995975851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194683517574270085327967801 146012638180702563995975851)
  ·
    refine ⟨219018957271053845993963777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146012638180702563995975851 219018957271053845993963777)
    ·
      refine ⟨164264217953290384495472833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219018957271053845993963777 164264217953290384495472833)
      ·
        refine ⟨123198163464967788371604625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164264217953290384495472833 123198163464967788371604625)
        ·
          refine ⟨92398622598725841278703469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123198163464967788371604625 92398622598725841278703469)
          ·
            refine ⟨34649483474522190479513801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92398622598725841278703469 34649483474522190479513801)
            ·
              refine ⟨25987112605891642859635351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34649483474522190479513801 25987112605891642859635351)
              ·
                refine ⟨38980668908837464289453027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25987112605891642859635351 38980668908837464289453027)
                ·
                  refine ⟨58471003363256196434179541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38980668908837464289453027 58471003363256196434179541)
                  ·
                    refine ⟨1370414141326317103926083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58471003363256196434179541 1370414141326317103926083)
                    ·
                      rfl

theorem cell23_8006616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_8006616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006616 prefixEnd_8006616 := by exact prefixLift 8006616
  have htrace : WordTrace (prefixWord ++ tailWord_8006616) baseStart_8006616 baseEnd_8006616 := by
    simpa [prefixWord, tailWord_8006616, baseEnd_8006616] using wordTrace_append hprefix tailTrace_8006616
  have hstable : (prefixWord ++ tailWord_8006616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006616).length < 2 ^ (prefixWord ++ tailWord_8006616).sum := by decide
  have hdescent : baseEnd_8006616 < baseStart_8006616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006653 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_8006653 : Nat := 118140960795 + 8006653 * 2 ^ 59
def prefixEnd_8006653 : Nat := 4983230072969 + 3 ^ 40 * 8006653 * 2
def baseEnd_8006653 : Nat := 4111261422763167667015579

theorem tailTrace_8006653 : CollatzResearch.WordTrace tailWord_8006653 prefixEnd_8006653 4111261422763167667015579 := by
  unfold tailWord_8006653
  simp only [CollatzResearch.WordTrace]
  refine ⟨292026625862271083311048613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194684417241514055540699075 292026625862271083311048613)
  ·
    refine ⟨54754992349175828120821615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292026625862271083311048613 54754992349175828120821615)
    ·
      refine ⟨82132488523763742181232423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54754992349175828120821615 82132488523763742181232423)
      ·
        refine ⟨123198732785645613271848635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82132488523763742181232423 123198732785645613271848635)
        ·
          refine ⟨184798099178468419907772953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123198732785645613271848635 184798099178468419907772953)
          ·
            refine ⟨138598574383851314930829715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184798099178468419907772953 138598574383851314930829715)
            ·
              refine ⟨207897861575776972396244573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138598574383851314930829715 207897861575776972396244573)
              ·
                refine ⟨77961698090916364648591715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207897861575776972396244573 77961698090916364648591715)
                ·
                  refine ⟨116942547136374546972887573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77961698090916364648591715 116942547136374546972887573)
                  ·
                    refine ⟨5481681897017556889354105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116942547136374546972887573 5481681897017556889354105)
                    ·
                      refine ⟨4111261422763167667015579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481681897017556889354105 4111261422763167667015579)
                      ·
                        rfl

theorem cell23_8006653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_8006653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006653 prefixEnd_8006653 := by exact prefixLift 8006653
  have htrace : WordTrace (prefixWord ++ tailWord_8006653) baseStart_8006653 baseEnd_8006653 := by
    simpa [prefixWord, tailWord_8006653, baseEnd_8006653] using wordTrace_append hprefix tailTrace_8006653
  have hstable : (prefixWord ++ tailWord_8006653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006653).length < 2 ^ (prefixWord ++ tailWord_8006653).sum := by decide
  have hdescent : baseEnd_8006653 < baseStart_8006653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006663 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 5, 4]
def baseStart_8006663 : Nat := 118140960795 + 8006663 * 2 ^ 59
def prefixEnd_8006663 : Nat := 4983230072969 + 3 ^ 40 * 8006663 * 2
def baseEnd_8006663 : Nat := 1370422185856570875963511

theorem tailTrace_8006663 : CollatzResearch.WordTrace tailWord_8006663 prefixEnd_8006663 1370422185856570875963511 := by
  unfold tailWord_8006663
  simp only [CollatzResearch.WordTrace]
  refine ⟨292026990592234855018912643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194684660394823236679275095 292026990592234855018912643)
  ·
    refine ⟨438040485888352282528368965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292026990592234855018912643 438040485888352282528368965)
    ·
      refine ⟨82132591104066052974069181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438040485888352282528368965 82132591104066052974069181)
      ·
        refine ⟨30799721664024769865275943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82132591104066052974069181 30799721664024769865275943)
        ·
          refine ⟨46199582496037154797913915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30799721664024769865275943 46199582496037154797913915)
          ·
            refine ⟨69299373744055732196870873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46199582496037154797913915 69299373744055732196870873)
            ·
              refine ⟨51974530308041799147653155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69299373744055732196870873 51974530308041799147653155)
              ·
                refine ⟨77961795462062698721479733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51974530308041799147653155 77961795462062698721479733)
                ·
                  refine ⟨7308918324568378005138725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77961795462062698721479733 7308918324568378005138725)
                  ·
                    refine ⟨1370422185856570875963511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7308918324568378005138725 1370422185856570875963511)
                    ·
                      rfl

theorem cell23_8006663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_8006663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006663 prefixEnd_8006663 := by exact prefixLift 8006663
  have htrace : WordTrace (prefixWord ++ tailWord_8006663) baseStart_8006663 baseEnd_8006663 := by
    simpa [prefixWord, tailWord_8006663, baseEnd_8006663] using wordTrace_append hprefix tailTrace_8006663
  have hstable : (prefixWord ++ tailWord_8006663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006663).length < 2 ^ (prefixWord ++ tailWord_8006663).sum := by decide
  have hdescent : baseEnd_8006663 < baseStart_8006663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006670 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_8006670 : Nat := 118140960795 + 8006670 * 2 ^ 59
def prefixEnd_8006670 : Nat := 4983230072969 + 3 ^ 40 * 8006670 * 2
def baseEnd_8006670 : Nat := 4111270151934294100503001

theorem tailTrace_8006670 : CollatzResearch.WordTrace tailWord_8006670 prefixEnd_8006670 4111270151934294100503001 := by
  unfold tailWord_8006670
  simp only [CollatzResearch.WordTrace]
  refine ⟨36503405737901186901802183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194684830602139663476278309 36503405737901186901802183)
  ·
    refine ⟨54755108606851780352703275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36503405737901186901802183 54755108606851780352703275)
    ·
      refine ⟨82132662910277670529054913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54755108606851780352703275 82132662910277670529054913)
      ·
        refine ⟨61599497182708252896791185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82132662910277670529054913 61599497182708252896791185)
        ·
          refine ⟨46199622887031189672593389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61599497182708252896791185 46199622887031189672593389)
          ·
            refine ⟨17324858582636696127222521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46199622887031189672593389 17324858582636696127222521)
            ·
              refine ⟨12993643936977522095416891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17324858582636696127222521 12993643936977522095416891)
              ·
                refine ⟨19490465905466283143125337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12993643936977522095416891 19490465905466283143125337)
                ·
                  refine ⟨14617849429099712357344003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19490465905466283143125337 14617849429099712357344003)
                  ·
                    refine ⟨21926774143649568536016005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14617849429099712357344003 21926774143649568536016005)
                    ·
                      refine ⟨4111270151934294100503001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21926774143649568536016005 4111270151934294100503001)
                      ·
                        rfl

theorem cell23_8006670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_8006670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006670 prefixEnd_8006670 := by exact prefixLift 8006670
  have htrace : WordTrace (prefixWord ++ tailWord_8006670) baseStart_8006670 baseEnd_8006670 := by
    simpa [prefixWord, tailWord_8006670, baseEnd_8006670] using wordTrace_append hprefix tailTrace_8006670
  have hstable : (prefixWord ++ tailWord_8006670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006670).length < 2 ^ (prefixWord ++ tailWord_8006670).sum := by decide
  have hdescent : baseEnd_8006670 < baseStart_8006670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006690 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_8006690 : Nat := 118140960795 + 8006690 * 2 ^ 59
def prefixEnd_8006690 : Nat := 4983230072969 + 3 ^ 40 * 8006690 * 2
def baseEnd_8006690 : Nat := 4111280421547384022252909

theorem tailTrace_8006690 : CollatzResearch.WordTrace tailWord_8006690 prefixEnd_8006690 4111280421547384022252909 := by
  unfold tailWord_8006690
  simp only [CollatzResearch.WordTrace]
  refine ⟨73006993840784259657536381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194685316908758025753430349 73006993840784259657536381)
  ·
    refine ⟨27377622690294097371576143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73006993840784259657536381 27377622690294097371576143)
    ·
      refine ⟨41066434035441146057364215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27377622690294097371576143 41066434035441146057364215)
      ·
        refine ⟨61599651053161719086046323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41066434035441146057364215 61599651053161719086046323)
        ·
          refine ⟨92399476579742578629069485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61599651053161719086046323 92399476579742578629069485)
          ·
            refine ⟨34649803717403466985901057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92399476579742578629069485 34649803717403466985901057)
            ·
              refine ⟨25987352788052600239425793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34649803717403466985901057 25987352788052600239425793)
              ·
                refine ⟨19490514591039450179569345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25987352788052600239425793 19490514591039450179569345)
                ·
                  refine ⟨14617885943279587634677009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19490514591039450179569345 14617885943279587634677009)
                  ·
                    refine ⟨10963414457459690726007757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14617885943279587634677009 10963414457459690726007757)
                    ·
                      refine ⟨4111280421547384022252909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10963414457459690726007757 4111280421547384022252909)
                      ·
                        rfl

theorem cell23_8006690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_8006690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006690 prefixEnd_8006690 := by exact prefixLift 8006690
  have htrace : WordTrace (prefixWord ++ tailWord_8006690) baseStart_8006690 baseEnd_8006690 := by
    simpa [prefixWord, tailWord_8006690, baseEnd_8006690] using wordTrace_append hprefix tailTrace_8006690
  have hstable : (prefixWord ++ tailWord_8006690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006690).length < 2 ^ (prefixWord ++ tailWord_8006690).sum := by decide
  have hdescent : baseEnd_8006690 < baseStart_8006690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006693 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 6]
def baseStart_8006693 : Nat := 118140960795 + 8006693 * 2 ^ 59
def prefixEnd_8006693 : Nat := 4983230072969 + 3 ^ 40 * 8006693 * 2
def baseEnd_8006693 : Nat := 456809106887705278946155

theorem tailTrace_8006693 : CollatzResearch.WordTrace tailWord_8006693 prefixEnd_8006693 456809106887705278946155 := by
  unfold tailWord_8006693
  simp only [CollatzResearch.WordTrace]
  refine ⟨292028084782126170142504733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194685389854750780095003155 292028084782126170142504733)
  ·
    refine ⟨109510531793297313803439275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292028084782126170142504733 109510531793297313803439275)
    ·
      refine ⟨164265797689945970705158913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109510531793297313803439275 164265797689945970705158913)
      ·
        refine ⟨123199348267459478028869185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164265797689945970705158913 123199348267459478028869185)
        ·
          refine ⟨92399511200594608521651889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123199348267459478028869185 92399511200594608521651889)
          ·
            refine ⟨69299633400445956391238917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92399511200594608521651889 69299633400445956391238917)
            ·
              refine ⟨12993681262583616823357297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69299633400445956391238917 12993681262583616823357297)
              ·
                refine ⟨9745260946937712617517973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12993681262583616823357297 9745260946937712617517973)
                ·
                  refine ⟨456809106887705278946155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9745260946937712617517973 456809106887705278946155)
                  ·
                    rfl

theorem cell23_8006693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_8006693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006693 prefixEnd_8006693 := by exact prefixLift 8006693
  have htrace : WordTrace (prefixWord ++ tailWord_8006693) baseStart_8006693 baseEnd_8006693 := by
    simpa [prefixWord, tailWord_8006693, baseEnd_8006693] using wordTrace_append hprefix tailTrace_8006693
  have hstable : (prefixWord ++ tailWord_8006693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006693).length < 2 ^ (prefixWord ++ tailWord_8006693).sum := by decide
  have hdescent : baseEnd_8006693 < baseStart_8006693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006710 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_8006710 : Nat := 118140960795 + 8006710 * 2 ^ 59
def prefixEnd_8006710 : Nat := 4983230072969 + 3 ^ 40 * 8006710 * 2
def baseEnd_8006710 : Nat := 456810076795608216000313

theorem tailTrace_8006710 : CollatzResearch.WordTrace tailWord_8006710 prefixEnd_8006710 456810076795608216000313 := by
  unfold tailWord_8006710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18251794051441536377867099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194685803215376388030582389 18251794051441536377867099)
  ·
    refine ⟨27377691077162304566800649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18251794051441536377867099 27377691077162304566800649)
    ·
      refine ⟨20533268307871728425100487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27377691077162304566800649 20533268307871728425100487)
      ·
        refine ⟨30799902461807592637650731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20533268307871728425100487 30799902461807592637650731)
        ·
          refine ⟨46199853692711388956476097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30799902461807592637650731 46199853692711388956476097)
          ·
            refine ⟨34649890269533541717357073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46199853692711388956476097 34649890269533541717357073)
            ·
              refine ⟨25987417702150156288017805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34649890269533541717357073 25987417702150156288017805)
              ·
                refine ⟨9745281638306308608006677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25987417702150156288017805 9745281638306308608006677)
                ·
                  refine ⟨456810076795608216000313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9745281638306308608006677 456810076795608216000313)
                  ·
                    rfl

theorem cell23_8006710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_8006710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006710 prefixEnd_8006710 := by exact prefixLift 8006710
  have htrace : WordTrace (prefixWord ++ tailWord_8006710) baseStart_8006710 baseEnd_8006710 := by
    simpa [prefixWord, tailWord_8006710, baseEnd_8006710] using wordTrace_append hprefix tailTrace_8006710
  have hstable : (prefixWord ++ tailWord_8006710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006710).length < 2 ^ (prefixWord ++ tailWord_8006710).sum := by decide
  have hdescent : baseEnd_8006710 < baseStart_8006710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006720 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 3, 1, 3]
def baseStart_8006720 : Nat := 118140960795 + 8006720 * 2 ^ 59
def prefixEnd_8006720 : Nat := 4983230072969 + 3 ^ 40 * 8006720 * 2
def baseEnd_8006720 : Nat := 4111295825967018904877771

theorem tailTrace_8006720 : CollatzResearch.WordTrace tailWord_8006720 prefixEnd_8006720 4111295825967018904877771 := by
  unfold tailWord_8006720
  simp only [CollatzResearch.WordTrace]
  refine ⟨146014534776514176876868807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194686046368685569169158409 146014534776514176876868807)
  ·
    refine ⟨219021802164771265315303211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146014534776514176876868807 219021802164771265315303211)
    ·
      refine ⟨328532703247156897972954817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219021802164771265315303211 328532703247156897972954817)
      ·
        refine ⟨246399527435367673479716113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328532703247156897972954817 246399527435367673479716113)
        ·
          refine ⟨184799645576525755109787085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246399527435367673479716113 184799645576525755109787085)
          ·
            refine ⟨69299867091197158166170157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184799645576525755109787085 69299867091197158166170157)
            ·
              refine ⟨25987450159198934312313809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69299867091197158166170157 25987450159198934312313809)
              ·
                refine ⟨19490587619399200734235357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25987450159198934312313809 19490587619399200734235357)
                ·
                  refine ⟨7308970357274700275338259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19490587619399200734235357 7308970357274700275338259)
                  ·
                    refine ⟨10963455535912050413007389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7308970357274700275338259 10963455535912050413007389)
                    ·
                      refine ⟨4111295825967018904877771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10963455535912050413007389 4111295825967018904877771)
                      ·
                        rfl

theorem cell23_8006720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_8006720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006720 prefixEnd_8006720 := by exact prefixLift 8006720
  have htrace : WordTrace (prefixWord ++ tailWord_8006720) baseStart_8006720 baseEnd_8006720 := by
    simpa [prefixWord, tailWord_8006720, baseEnd_8006720] using wordTrace_append hprefix tailTrace_8006720
  have hstable : (prefixWord ++ tailWord_8006720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006720).length < 2 ^ (prefixWord ++ tailWord_8006720).sum := by decide
  have hdescent : baseEnd_8006720 < baseStart_8006720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006723 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 1, 5]
def baseStart_8006723 : Nat := 118140960795 + 8006723 * 2 ^ 59
def prefixEnd_8006723 : Nat := 4983230072969 + 3 ^ 40 * 8006723 * 2
def baseEnd_8006723 : Nat := 1370432455469660797713419

theorem tailTrace_8006723 : CollatzResearch.WordTrace tailWord_8006723 prefixEnd_8006723 1370432455469660797713419 := by
  unfold tailWord_8006723
  simp only [CollatzResearch.WordTrace]
  refine ⟨292029178972017485266096823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194686119314678323510731215 292029178972017485266096823)
  ·
    refine ⟨438043768458026227899145235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292029178972017485266096823 438043768458026227899145235)
    ·
      refine ⟨657065652687039341848717853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438043768458026227899145235 657065652687039341848717853)
      ·
        refine ⟨246399619757639753193269195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 657065652687039341848717853 246399619757639753193269195)
        ·
          refine ⟨369599429636459629789903793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246399619757639753193269195 369599429636459629789903793)
          ·
            refine ⟨277199572227344722342427845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369599429636459629789903793 277199572227344722342427845)
            ·
              refine ⟨51974919792627135439205221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277199572227344722342427845 51974919792627135439205221)
              ·
                refine ⟨9745297461117587894850979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51974919792627135439205221 9745297461117587894850979)
                ·
                  refine ⟨14617946191676381842276469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9745297461117587894850979 14617946191676381842276469)
                  ·
                    refine ⟨1370432455469660797713419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14617946191676381842276469 1370432455469660797713419)
                    ·
                      rfl

theorem cell23_8006723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 5].length) (baseStart_8006723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006723 prefixEnd_8006723 := by exact prefixLift 8006723
  have htrace : WordTrace (prefixWord ++ tailWord_8006723) baseStart_8006723 baseEnd_8006723 := by
    simpa [prefixWord, tailWord_8006723, baseEnd_8006723] using wordTrace_append hprefix tailTrace_8006723
  have hstable : (prefixWord ++ tailWord_8006723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006723).length < 2 ^ (prefixWord ++ tailWord_8006723).sum := by decide
  have hdescent : baseEnd_8006723 < baseStart_8006723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006737 : List Nat := [1, 2, 2, 1, 3, 1, 3, 5, 1, 1, 3]
def baseStart_8006737 : Nat := 118140960795 + 8006737 * 2 ^ 59
def prefixEnd_8006737 : Nat := 4983230072969 + 3 ^ 40 * 8006737 * 2
def baseEnd_8006737 : Nat := 4111304555138145338365193

theorem tailTrace_8006737 : CollatzResearch.WordTrace tailWord_8006737 prefixEnd_8006737 4111304555138145338365193 := by
  unfold tailWord_8006737
  simp only [CollatzResearch.WordTrace]
  refine ⟨292029689593966765657106465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194686459729311177104737643 292029689593966765657106465)
  ·
    refine ⟨219022267195475074242829849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292029689593966765657106465 219022267195475074242829849)
    ·
      refine ⟨164266700396606305682122387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219022267195475074242829849 164266700396606305682122387)
      ·
        refine ⟨246400050594909458523183581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164266700396606305682122387 246400050594909458523183581)
        ·
          refine ⟨92400018973091046946193843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246400050594909458523183581 92400018973091046946193843)
          ·
            refine ⟨138600028459636570419290765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92400018973091046946193843 138600028459636570419290765)
            ·
              refine ⟨51975010672363713907234037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138600028459636570419290765 51975010672363713907234037)
              ·
                refine ⟨4872657250534098178803191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51975010672363713907234037 4872657250534098178803191)
                ·
                  refine ⟨7308985875801147268204787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872657250534098178803191 7308985875801147268204787)
                  ·
                    refine ⟨10963478813701720902307181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7308985875801147268204787 10963478813701720902307181)
                    ·
                      refine ⟨4111304555138145338365193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10963478813701720902307181 4111304555138145338365193)
                      ·
                        rfl

theorem cell23_8006737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_8006737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006737 prefixEnd_8006737 := by exact prefixLift 8006737
  have htrace : WordTrace (prefixWord ++ tailWord_8006737) baseStart_8006737 baseEnd_8006737 := by
    simpa [prefixWord, tailWord_8006737, baseEnd_8006737] using wordTrace_append hprefix tailTrace_8006737
  have hstable : (prefixWord ++ tailWord_8006737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006737).length < 2 ^ (prefixWord ++ tailWord_8006737).sum := by decide
  have hdescent : baseEnd_8006737 < baseStart_8006737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006754 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_8006754 : Nat := 118140960795 + 8006754 * 2 ^ 59
def prefixEnd_8006754 : Nat := 4983230072969 + 3 ^ 40 * 8006754 * 2
def baseEnd_8006754 : Nat := 4111313284309271771852615

theorem tailTrace_8006754 : CollatzResearch.WordTrace tailWord_8006754 prefixEnd_8006754 4111313284309271771852615 := by
  unfold tailWord_8006754
  simp only [CollatzResearch.WordTrace]
  refine ⟨73007577408726294390118829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194686873089936785040316877 73007577408726294390118829)
  ·
    refine ⟨27377841528272360396294561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73007577408726294390118829 27377841528272360396294561)
    ·
      refine ⟨20533381146204270297220921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27377841528272360396294561 20533381146204270297220921)
      ·
        refine ⟨15400035859653202722915691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20533381146204270297220921 15400035859653202722915691)
        ·
          refine ⟨23100053789479804084373537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15400035859653202722915691 23100053789479804084373537)
          ·
            refine ⟨17325040342109853063280153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23100053789479804084373537 17325040342109853063280153)
            ·
              refine ⟨12993780256582389797460115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17325040342109853063280153 12993780256582389797460115)
              ·
                refine ⟨19490670384873584696190173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12993780256582389797460115 19490670384873584696190173)
                ·
                  refine ⟨7309001394327594261071315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19490670384873584696190173 7309001394327594261071315)
                  ·
                    refine ⟨10963502091491391391606973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7309001394327594261071315 10963502091491391391606973)
                    ·
                      refine ⟨4111313284309271771852615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10963502091491391391606973 4111313284309271771852615)
                      ·
                        rfl

theorem cell23_8006754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_8006754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006754 prefixEnd_8006754 := by exact prefixLift 8006754
  have htrace : WordTrace (prefixWord ++ tailWord_8006754) baseStart_8006754 baseEnd_8006754 := by
    simpa [prefixWord, tailWord_8006754, baseEnd_8006754] using wordTrace_append hprefix tailTrace_8006754
  have hstable : (prefixWord ++ tailWord_8006754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006754).length < 2 ^ (prefixWord ++ tailWord_8006754).sum := by decide
  have hdescent : baseEnd_8006754 < baseStart_8006754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006777 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 4]
def baseStart_8006777 : Nat := 118140960795 + 8006777 * 2 ^ 59
def prefixEnd_8006777 : Nat := 4983230072969 + 3 ^ 40 * 8006777 * 2
def baseEnd_8006777 : Nat := 4111325094364325181865009

theorem tailTrace_8006777 : CollatzResearch.WordTrace tailWord_8006777 prefixEnd_8006777 4111325094364325181865009 := by
  unfold tailWord_8006777
  simp only [CollatzResearch.WordTrace]
  refine ⟨292031148513821852488562585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194687432342547901659041723 292031148513821852488562585)
  ·
    refine ⟨219023361385366389366421939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292031148513821852488562585 219023361385366389366421939)
    ·
      refine ⟨328535042078049584049632909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219023361385366389366421939 328535042078049584049632909)
      ·
        refine ⟨123200640779268594018612341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328535042078049584049632909 123200640779268594018612341)
        ·
          refine ⟨11550060073056430689244907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123200640779268594018612341 11550060073056430689244907)
          ·
            refine ⟨17325090109584646033867361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11550060073056430689244907 17325090109584646033867361)
            ·
              refine ⟨12993817582188484525400521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17325090109584646033867361 12993817582188484525400521)
              ·
                refine ⟨9745363186641363394050391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12993817582188484525400521 9745363186641363394050391)
                ·
                  refine ⟨14618044779962045091075587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9745363186641363394050391 14618044779962045091075587)
                  ·
                    refine ⟨21927067169943067636613381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14618044779962045091075587 21927067169943067636613381)
                    ·
                      refine ⟨4111325094364325181865009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21927067169943067636613381 4111325094364325181865009)
                      ·
                        rfl

theorem cell23_8006777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_8006777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006777 prefixEnd_8006777 := by exact prefixLift 8006777
  have htrace : WordTrace (prefixWord ++ tailWord_8006777) baseStart_8006777 baseEnd_8006777 := by
    simpa [prefixWord, tailWord_8006777, baseEnd_8006777] using wordTrace_append hprefix tailTrace_8006777
  have hstable : (prefixWord ++ tailWord_8006777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006777).length < 2 ^ (prefixWord ++ tailWord_8006777).sum := by decide
  have hdescent : baseEnd_8006777 < baseStart_8006777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006813 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_8006813 : Nat := 118140960795 + 8006813 * 2 ^ 59
def prefixEnd_8006813 : Nat := 4983230072969 + 3 ^ 40 * 8006813 * 2
def baseEnd_8006813 : Nat := 1370447859889295680338281

theorem tailTrace_8006813 : CollatzResearch.WordTrace tailWord_8006813 prefixEnd_8006813 1370447859889295680338281 := by
  unfold tailWord_8006813
  simp only [CollatzResearch.WordTrace]
  refine ⟨292032461541691430636873093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194688307694460953757915395 292032461541691430636873093)
  ·
    refine ⟨54756086539067143244413705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292032461541691430636873093 54756086539067143244413705)
    ·
      refine ⟨41067064904300357433310279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54756086539067143244413705 41067064904300357433310279)
      ·
        refine ⟨61600597356450536149965419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41067064904300357433310279 61600597356450536149965419)
        ·
          refine ⟨92400896034675804224948129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61600597356450536149965419 92400896034675804224948129)
          ·
            refine ⟨69300672026006853168711097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92400896034675804224948129 69300672026006853168711097)
            ·
              refine ⟨51975504019505139876533323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69300672026006853168711097 51975504019505139876533323)
              ·
                refine ⟨77963256029257709814799985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51975504019505139876533323 77963256029257709814799985)
                ·
                  refine ⟨58472442021943282361099989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77963256029257709814799985 58472442021943282361099989)
                  ·
                    refine ⟨1370447859889295680338281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58472442021943282361099989 1370447859889295680338281)
                    ·
                      rfl

theorem cell23_8006813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_8006813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006813 prefixEnd_8006813 := by exact prefixLift 8006813
  have htrace : WordTrace (prefixWord ++ tailWord_8006813) baseStart_8006813 baseEnd_8006813 := by
    simpa [prefixWord, tailWord_8006813, baseEnd_8006813] using wordTrace_append hprefix tailTrace_8006813
  have hstable : (prefixWord ++ tailWord_8006813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006813).length < 2 ^ (prefixWord ++ tailWord_8006813).sum := by decide
  have hdescent : baseEnd_8006813 < baseStart_8006813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006873 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 7]
def baseStart_8006873 : Nat := 118140960795 + 8006873 * 2 ^ 59
def prefixEnd_8006873 : Nat := 4983230072969 + 3 ^ 40 * 8006873 * 2
def baseEnd_8006873 : Nat := 456819376500795200696063

theorem tailTrace_8006873 : CollatzResearch.WordTrace tailWord_8006873 prefixEnd_8006873 456819376500795200696063 := by
  unfold tailWord_8006873
  simp only [CollatzResearch.WordTrace]
  refine ⟨292034649921474060884057273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194689766614316040589371515 292034649921474060884057273)
  ·
    refine ⟨219025987441105545663042955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292034649921474060884057273 219025987441105545663042955)
    ·
      refine ⟨328538981161658318494564433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219025987441105545663042955 328538981161658318494564433)
      ·
        refine ⟨246404235871243738870923325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328538981161658318494564433 246404235871243738870923325)
        ·
          refine ⟨92401588451716402076596247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246404235871243738870923325 92401588451716402076596247)
          ·
            refine ⟨138602382677574603114894371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92401588451716402076596247 138602382677574603114894371)
            ·
              refine ⟨207903574016361904672341557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138602382677574603114894371 207903574016361904672341557)
              ·
                refine ⟨19490960064033928563032021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207903574016361904672341557 19490960064033928563032021)
                ·
                  refine ⟨456819376500795200696063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19490960064033928563032021 456819376500795200696063)
                  ·
                    rfl

theorem cell23_8006873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 7].length) (baseStart_8006873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006873 prefixEnd_8006873 := by exact prefixLift 8006873
  have htrace : WordTrace (prefixWord ++ tailWord_8006873) baseStart_8006873 baseEnd_8006873 := by
    simpa [prefixWord, tailWord_8006873, baseEnd_8006873] using wordTrace_append hprefix tailTrace_8006873
  have hstable : (prefixWord ++ tailWord_8006873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006873).length < 2 ^ (prefixWord ++ tailWord_8006873).sum := by decide
  have hdescent : baseEnd_8006873 < baseStart_8006873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006877 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_8006877 : Nat := 118140960795 + 8006877 * 2 ^ 59
def prefixEnd_8006877 : Nat := 4983230072969 + 3 ^ 40 * 8006877 * 2
def baseEnd_8006877 : Nat := 1370458814143258263538183

theorem tailTrace_8006877 : CollatzResearch.WordTrace tailWord_8006877 prefixEnd_8006877 1370458814143258263538183 := by
  unfold tailWord_8006877
  simp only [CollatzResearch.WordTrace]
  refine ⟨292034795813459569567202885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194689863875639713044801923 292034795813459569567202885)
  ·
    refine ⟨54756524215023669293850541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292034795813459569567202885 54756524215023669293850541)
    ·
      refine ⟨20533696580633875985193953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54756524215023669293850541 20533696580633875985193953)
      ·
        refine ⟨15400272435475406988895465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20533696580633875985193953 15400272435475406988895465)
        ·
          refine ⟨11550204326606555241671599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15400272435475406988895465 11550204326606555241671599)
          ·
            refine ⟨17325306489909832862507399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11550204326606555241671599 17325306489909832862507399)
            ·
              refine ⟨25987959734864749293761099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17325306489909832862507399 25987959734864749293761099)
              ·
                refine ⟨38981939602297123940641649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25987959734864749293761099 38981939602297123940641649)
                ·
                  refine ⟨29236454701722842955481237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38981939602297123940641649 29236454701722842955481237)
                  ·
                    refine ⟨1370458814143258263538183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29236454701722842955481237 1370458814143258263538183)
                    ·
                      rfl

theorem cell23_8006877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_8006877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006877 prefixEnd_8006877 := by exact prefixLift 8006877
  have htrace : WordTrace (prefixWord ++ tailWord_8006877) baseStart_8006877 baseEnd_8006877 := by
    simpa [prefixWord, tailWord_8006877, baseEnd_8006877] using wordTrace_append hprefix tailTrace_8006877
  have hstable : (prefixWord ++ tailWord_8006877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006877).length < 2 ^ (prefixWord ++ tailWord_8006877).sum := by decide
  have hdescent : baseEnd_8006877 < baseStart_8006877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006880 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_8006880 : Nat := 118140960795 + 8006880 * 2 ^ 59
def prefixEnd_8006880 : Nat := 4983230072969 + 3 ^ 40 * 8006880 * 2
def baseEnd_8006880 : Nat := 4111377982871738278877035

theorem tailTrace_8006880 : CollatzResearch.WordTrace tailWord_8006880 prefixEnd_8006880 4111377982871738278877035 := by
  unfold tailWord_8006880
  simp only [CollatzResearch.WordTrace]
  refine ⟨146017452616224350539781047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194689936821632467386374729 146017452616224350539781047)
  ·
    refine ⟨219026178924336525809671571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146017452616224350539781047 219026178924336525809671571)
    ·
      refine ⟨328539268386504788714507357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219026178924336525809671571 328539268386504788714507357)
      ·
        refine ⟨123202225644939295767940259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328539268386504788714507357 123202225644939295767940259)
        ·
          refine ⟨184803338467408943651910389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123202225644939295767940259 184803338467408943651910389)
          ·
            refine ⟨17325312981319588467366599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184803338467408943651910389 17325312981319588467366599)
            ·
              refine ⟨25987969471979382701049899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17325312981319588467366599 25987969471979382701049899)
              ·
                refine ⟨38981954207969074051574849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25987969471979382701049899 38981954207969074051574849)
                ·
                  refine ⟨29236465655976805538681137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38981954207969074051574849 29236465655976805538681137)
                  ·
                    refine ⟨21927349241982604154010853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29236465655976805538681137 21927349241982604154010853)
                    ·
                      refine ⟨4111377982871738278877035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21927349241982604154010853 4111377982871738278877035)
                      ·
                        rfl

theorem cell23_8006880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_8006880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006880 prefixEnd_8006880 := by exact prefixLift 8006880
  have htrace : WordTrace (prefixWord ++ tailWord_8006880) baseStart_8006880 baseEnd_8006880 := by
    simpa [prefixWord, tailWord_8006880, baseEnd_8006880] using wordTrace_append hprefix tailTrace_8006880
  have hstable : (prefixWord ++ tailWord_8006880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006880).length < 2 ^ (prefixWord ++ tailWord_8006880).sum := by decide
  have hdescent : baseEnd_8006880 < baseStart_8006880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006884 : List Nat := [2, 3, 1, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_8006884 : Nat := 118140960795 + 8006884 * 2 ^ 59
def prefixEnd_8006884 : Nat := 4983230072969 + 3 ^ 40 * 8006884 * 2
def baseEnd_8006884 : Nat := 4111380036794356263227017

theorem tailTrace_8006884 : CollatzResearch.WordTrace tailWord_8006884 prefixEnd_8006884 4111380036794356263227017 := by
  unfold tailWord_8006884
  simp only [CollatzResearch.WordTrace]
  refine ⟨146017525562217104881353853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194690034082956139841805137 146017525562217104881353853)
  ·
    refine ⟨54756572085831414330507695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146017525562217104881353853 54756572085831414330507695)
    ·
      refine ⟨82134858128747121495761543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54756572085831414330507695 82134858128747121495761543)
      ·
        refine ⟨123202287193120682243642315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82134858128747121495761543 123202287193120682243642315)
        ·
          refine ⟨184803430789681023365463473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123202287193120682243642315 184803430789681023365463473)
          ·
            refine ⟨138602573092260767524097605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184803430789681023365463473 138602573092260767524097605)
            ·
              refine ⟨25987982454798893910768301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138602573092260767524097605 25987982454798893910768301)
              ·
                refine ⟨9745493420549585216538113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25987982454798893910768301 9745493420549585216538113)
                ·
                  refine ⟨7309120065412188912403585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9745493420549585216538113 7309120065412188912403585)
                  ·
                    refine ⟨5481840049059141684302689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7309120065412188912403585 5481840049059141684302689)
                    ·
                      refine ⟨4111380036794356263227017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5481840049059141684302689 4111380036794356263227017)
                      ·
                        rfl

theorem cell23_8006884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_8006884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006884 prefixEnd_8006884 := by exact prefixLift 8006884
  have htrace : WordTrace (prefixWord ++ tailWord_8006884) baseStart_8006884 baseEnd_8006884 := by
    simpa [prefixWord, tailWord_8006884, baseEnd_8006884] using wordTrace_append hprefix tailTrace_8006884
  have hstable : (prefixWord ++ tailWord_8006884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006884).length < 2 ^ (prefixWord ++ tailWord_8006884).sum := by decide
  have hdescent : baseEnd_8006884 < baseStart_8006884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006890 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 7]
def baseStart_8006890 : Nat := 118140960795 + 8006890 * 2 ^ 59
def prefixEnd_8006890 : Nat := 4983230072969 + 3 ^ 40 * 8006890 * 2
def baseEnd_8006890 : Nat := 456820346408698137750221

theorem tailTrace_8006890 : CollatzResearch.WordTrace tailWord_8006890 prefixEnd_8006890 456820346408698137750221 := by
  unfold tailWord_8006890
  simp only [CollatzResearch.WordTrace]
  refine ⟨73008817490603118196856531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194690179974941648524950749 73008817490603118196856531)
  ·
    refine ⟨109513226235904677295284797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73008817490603118196856531 109513226235904677295284797)
    ·
      refine ⟨41067459838464253985731799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109513226235904677295284797 41067459838464253985731799)
      ·
        refine ⟨61601189757696380978597699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41067459838464253985731799 61601189757696380978597699)
        ·
          refine ⟨92401784636544571467896549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61601189757696380978597699 92401784636544571467896549)
          ·
            refine ⟨17325334619352107150230603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92401784636544571467896549 17325334619352107150230603)
            ·
              refine ⟨25988001929028160725345905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17325334619352107150230603 25988001929028160725345905)
              ·
                refine ⟨19491001446771120544009429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25988001929028160725345905 19491001446771120544009429)
                ·
                  refine ⟨456820346408698137750221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19491001446771120544009429 456820346408698137750221)
                  ·
                    rfl

theorem cell23_8006890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_8006890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006890 prefixEnd_8006890 := by exact prefixLift 8006890
  have htrace : WordTrace (prefixWord ++ tailWord_8006890) baseStart_8006890 baseEnd_8006890 := by
    simpa [prefixWord, tailWord_8006890, baseEnd_8006890] using wordTrace_append hprefix tailTrace_8006890
  have hstable : (prefixWord ++ tailWord_8006890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006890).length < 2 ^ (prefixWord ++ tailWord_8006890).sum := by decide
  have hdescent : baseEnd_8006890 < baseStart_8006890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006903 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 1, 7]
def baseStart_8006903 : Nat := 118140960795 + 8006903 * 2 ^ 59
def prefixEnd_8006903 : Nat := 4983230072969 + 3 ^ 40 * 8006903 * 2
def baseEnd_8006903 : Nat := 1370463264308930562963143

theorem tailTrace_8006903 : CollatzResearch.WordTrace tailWord_8006903 prefixEnd_8006903 1370463264308930562963143 := by
  unfold tailWord_8006903
  simp only [CollatzResearch.WordTrace]
  refine ⟨292035744111365376007649363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194690496074243584005099575 292035744111365376007649363)
  ·
    refine ⟨438053616167048064011474045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292035744111365376007649363 438053616167048064011474045)
    ·
      refine ⟨164270106062643024004302767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438053616167048064011474045 164270106062643024004302767)
      ·
        refine ⟨246405159093964536006454151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164270106062643024004302767 246405159093964536006454151)
        ·
          refine ⟨369607738640946804009681227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246405159093964536006454151 369607738640946804009681227)
          ·
            refine ⟨554411607961420206014521841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369607738640946804009681227 554411607961420206014521841)
            ·
              refine ⟨415808705971065154510891381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554411607961420206014521841 415808705971065154510891381)
              ·
                refine ⟨38982066184787358235396067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 415808705971065154510891381 38982066184787358235396067)
                ·
                  refine ⟨58473099277181037353094101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38982066184787358235396067 58473099277181037353094101)
                  ·
                    refine ⟨1370463264308930562963143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58473099277181037353094101 1370463264308930562963143)
                    ·
                      rfl

theorem cell23_8006903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_8006903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006903 prefixEnd_8006903 := by exact prefixLift 8006903
  have htrace : WordTrace (prefixWord ++ tailWord_8006903) baseStart_8006903 baseEnd_8006903 := by
    simpa [prefixWord, tailWord_8006903, baseEnd_8006903] using wordTrace_append hprefix tailTrace_8006903
  have hstable : (prefixWord ++ tailWord_8006903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006903).length < 2 ^ (prefixWord ++ tailWord_8006903).sum := by decide
  have hdescent : baseEnd_8006903 < baseStart_8006903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006940 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_8006940 : Nat := 118140960795 + 8006940 * 2 ^ 59
def prefixEnd_8006940 : Nat := 4983230072969 + 3 ^ 40 * 8006940 * 2
def baseEnd_8006940 : Nat := 4111408791711008044126759

theorem tailTrace_8006940 : CollatzResearch.WordTrace tailWord_8006940 prefixEnd_8006940 4111408791711008044126759 := by
  unfold tailWord_8006940
  simp only [CollatzResearch.WordTrace]
  refine ⟨146018546806115665663373137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194691395741487554217830849 146018546806115665663373137)
  ·
    refine ⟨109513910104586749247529853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146018546806115665663373137 109513910104586749247529853)
    ·
      refine ⟨41067716289220030967823695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109513910104586749247529853 41067716289220030967823695)
      ·
        refine ⟨61601574433830046451735543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41067716289220030967823695 61601574433830046451735543)
        ·
          refine ⟨92402361650745069677603315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61601574433830046451735543 92402361650745069677603315)
          ·
            refine ⟨138603542476117604516404973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92402361650745069677603315 138603542476117604516404973)
            ·
              refine ⟨51976328428544101693651865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138603542476117604516404973 51976328428544101693651865)
              ·
                refine ⟨38982246321408076270238899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51976328428544101693651865 38982246321408076270238899)
                ·
                  refine ⟨58473369482112114405358349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38982246321408076270238899 58473369482112114405358349)
                  ·
                    refine ⟨21927513555792042902009381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58473369482112114405358349 21927513555792042902009381)
                    ·
                      refine ⟨4111408791711008044126759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21927513555792042902009381 4111408791711008044126759)
                      ·
                        rfl

theorem cell23_8006940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_8006940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006940 prefixEnd_8006940 := by exact prefixLift 8006940
  have htrace : WordTrace (prefixWord ++ tailWord_8006940) baseStart_8006940 baseEnd_8006940 := by
    simpa [prefixWord, tailWord_8006940, baseEnd_8006940] using wordTrace_append hprefix tailTrace_8006940
  have hstable : (prefixWord ++ tailWord_8006940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006940).length < 2 ^ (prefixWord ++ tailWord_8006940).sum := by decide
  have hdescent : baseEnd_8006940 < baseStart_8006940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006960 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 3]
def baseStart_8006960 : Nat := 118140960795 + 8006960 * 2 ^ 59
def prefixEnd_8006960 : Nat := 4983230072969 + 3 ^ 40 * 8006960 * 2
def baseEnd_8006960 : Nat := 4111419061324097965876667

theorem tailTrace_8006960 : CollatzResearch.WordTrace tailWord_8006960 prefixEnd_8006960 4111419061324097965876667 := by
  unfold tailWord_8006960
  simp only [CollatzResearch.WordTrace]
  refine ⟨146018911536079437371237167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194691882048105916494982889 146018911536079437371237167)
  ·
    refine ⟨219028367304119156056855751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146018911536079437371237167 219028367304119156056855751)
    ·
      refine ⟨328542550956178734085283627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219028367304119156056855751 328542550956178734085283627)
      ·
        refine ⟨492813826434268101127925441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328542550956178734085283627 492813826434268101127925441)
        ·
          refine ⟨369610369825701075845944081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492813826434268101127925441 369610369825701075845944081)
          ·
            refine ⟨277207777369275806884458061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369610369825701075845944081 277207777369275806884458061)
            ·
              refine ⟨103952916513478427581671773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277207777369275806884458061 103952916513478427581671773)
              ·
                refine ⟨38982343692554410343126915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103952916513478427581671773 38982343692554410343126915)
                ·
                  refine ⟨58473515538831615514690373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38982343692554410343126915 58473515538831615514690373)
                  ·
                    refine ⟨10963784163530927909004445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58473515538831615514690373 10963784163530927909004445)
                    ·
                      refine ⟨4111419061324097965876667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10963784163530927909004445 4111419061324097965876667)
                      ·
                        rfl

theorem cell23_8006960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 3].length) (baseStart_8006960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006960 prefixEnd_8006960 := by exact prefixLift 8006960
  have htrace : WordTrace (prefixWord ++ tailWord_8006960) baseStart_8006960 baseEnd_8006960 := by
    simpa [prefixWord, tailWord_8006960, baseEnd_8006960] using wordTrace_append hprefix tailTrace_8006960
  have hstable : (prefixWord ++ tailWord_8006960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006960).length < 2 ^ (prefixWord ++ tailWord_8006960).sum := by decide
  have hdescent : baseEnd_8006960 < baseStart_8006960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8006997 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 6]
def baseStart_8006997 : Nat := 118140960795 + 8006997 * 2 ^ 59
def prefixEnd_8006997 : Nat := 4983230072969 + 3 ^ 40 * 8006997 * 2
def baseEnd_8006997 : Nat := 456826451123146035679333

theorem tailTrace_8006997 : CollatzResearch.WordTrace tailWord_8006997 prefixEnd_8006997 456826451123146035679333 := by
  unfold tailWord_8006997
  simp only [CollatzResearch.WordTrace]
  refine ⟨292039172573024830061571245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194692781715349886707714163 292039172573024830061571245)
  ·
    refine ⟨109514689714884311273089217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292039172573024830061571245 109514689714884311273089217)
    ·
      refine ⟨82136017286163233454816913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109514689714884311273089217 82136017286163233454816913)
      ·
        refine ⟨61602012964622425091112685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82136017286163233454816913 61602012964622425091112685)
        ·
          refine ⟨23100754861733409409167257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61602012964622425091112685 23100754861733409409167257)
          ·
            refine ⟨17325566146300057056875443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23100754861733409409167257 17325566146300057056875443)
            ·
              refine ⟨25988349219450085585313165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17325566146300057056875443 25988349219450085585313165)
              ·
                refine ⟨9745630957293782094492437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25988349219450085585313165 9745630957293782094492437)
                ·
                  refine ⟨456826451123146035679333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9745630957293782094492437 456826451123146035679333)
                  ·
                    rfl

theorem cell23_8006997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_8006997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8006997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8006997 prefixEnd_8006997 := by exact prefixLift 8006997
  have htrace : WordTrace (prefixWord ++ tailWord_8006997) baseStart_8006997 baseEnd_8006997 := by
    simpa [prefixWord, tailWord_8006997, baseEnd_8006997] using wordTrace_append hprefix tailTrace_8006997
  have hstable : (prefixWord ++ tailWord_8006997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8006997).length < 2 ^ (prefixWord ++ tailWord_8006997).sum := by decide
  have hdescent : baseEnd_8006997 < baseStart_8006997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8006997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007007 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 3]
def baseStart_8007007 : Nat := 118140960795 + 8007007 * 2 ^ 59
def prefixEnd_8007007 : Nat := 4983230072969 + 3 ^ 40 * 8007007 * 2
def baseEnd_8007007 : Nat := 4111443194914859281988951

theorem tailTrace_8007007 : CollatzResearch.WordTrace tailWord_8007007 prefixEnd_8007007 4111443194914859281988951 := by
  unfold tailWord_8007007
  simp only [CollatzResearch.WordTrace]
  refine ⟨292039537302988601769435275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194693024868659067846290183 292039537302988601769435275)
  ·
    refine ⟨438059305954482902654152913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292039537302988601769435275 438059305954482902654152913)
    ·
      refine ⟨328544479465862176990614685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438059305954482902654152913 328544479465862176990614685)
      ·
        refine ⟨123204179799698316371480507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328544479465862176990614685 123204179799698316371480507)
        ·
          refine ⟨184806269699547474557220761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123204179799698316371480507 184806269699547474557220761)
          ·
            refine ⟨138604702274660605917915571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184806269699547474557220761 138604702274660605917915571)
            ·
              refine ⟨207907053411990908876873357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138604702274660605917915571 207907053411990908876873357)
              ·
                refine ⟨77965145029496590828827509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207907053411990908876873357 77965145029496590828827509)
                ·
                  refine ⟨7309232346515305390202579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77965145029496590828827509 7309232346515305390202579)
                  ·
                    refine ⟨10963848519772958085303869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7309232346515305390202579 10963848519772958085303869)
                    ·
                      refine ⟨4111443194914859281988951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10963848519772958085303869 4111443194914859281988951)
                      ·
                        rfl

theorem cell23_8007007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_8007007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007007 prefixEnd_8007007 := by exact prefixLift 8007007
  have htrace : WordTrace (prefixWord ++ tailWord_8007007) baseStart_8007007 baseEnd_8007007 := by
    simpa [prefixWord, tailWord_8007007, baseEnd_8007007] using wordTrace_append hprefix tailTrace_8007007
  have hstable : (prefixWord ++ tailWord_8007007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007007).length < 2 ^ (prefixWord ++ tailWord_8007007).sum := by decide
  have hdescent : baseEnd_8007007 < baseStart_8007007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007047 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_8007047 : Nat := 118140960795 + 8007047 * 2 ^ 59
def prefixEnd_8007047 : Nat := 4983230072969 + 3 ^ 40 * 8007047 * 2
def baseEnd_8007047 : Nat := 4111463734141039125488767

theorem tailTrace_8007047 : CollatzResearch.WordTrace tailWord_8007047 prefixEnd_8007047 4111463734141039125488767 := by
  unfold tailWord_8007047
  simp only [CollatzResearch.WordTrace]
  refine ⟨292040996222843688600891395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194693997481895792400594263 292040996222843688600891395)
  ·
    refine ⟨438061494334265532901337093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292040996222843688600891395 438061494334265532901337093)
    ·
      refine ⟨82136530187674787419000705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438061494334265532901337093 82136530187674787419000705)
      ·
        refine ⟨61602397640756090564250529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82136530187674787419000705 61602397640756090564250529)
        ·
          refine ⟨46201798230567067923187897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61602397640756090564250529 46201798230567067923187897)
          ·
            refine ⟨34651348672925300942390923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46201798230567067923187897 34651348672925300942390923)
            ·
              refine ⟨51977023009387951413586385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34651348672925300942390923 51977023009387951413586385)
              ·
                refine ⟨38982767257040963560189789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51977023009387951413586385 38982767257040963560189789)
                ·
                  refine ⟨14618537721390361335071171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38982767257040963560189789 14618537721390361335071171)
                  ·
                    refine ⟨21927806582085542002606757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14618537721390361335071171 21927806582085542002606757)
                    ·
                      refine ⟨4111463734141039125488767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21927806582085542002606757 4111463734141039125488767)
                      ·
                        rfl

theorem cell23_8007047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_8007047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007047 prefixEnd_8007047 := by exact prefixLift 8007047
  have htrace : WordTrace (prefixWord ++ tailWord_8007047) baseStart_8007047 baseEnd_8007047 := by
    simpa [prefixWord, tailWord_8007047, baseEnd_8007047] using wordTrace_append hprefix tailTrace_8007047
  have hstable : (prefixWord ++ tailWord_8007047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007047).length < 2 ^ (prefixWord ++ tailWord_8007047).sum := by decide
  have hdescent : baseEnd_8007047 < baseStart_8007047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007058 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_8007058 : Nat := 118140960795 + 8007058 * 2 ^ 59
def prefixEnd_8007058 : Nat := 4983230072969 + 3 ^ 40 * 8007058 * 2
def baseEnd_8007058 : Nat := 4111469382428238582451217

theorem tailTrace_8007058 : CollatzResearch.WordTrace tailWord_8007058 prefixEnd_8007058 4111469382428238582451217 := by
  unfold tailWord_8007058
  simp only [CollatzResearch.WordTrace]
  refine ⟨73010349356450959369885457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194694264950535891653027885 73010349356450959369885457)
  ·
    refine ⟨54757762017338219527414093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73010349356450959369885457 54757762017338219527414093)
    ·
      refine ⟨20534160756501832322780285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54757762017338219527414093 20534160756501832322780285)
      ·
        refine ⟨7700310283688187121042607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20534160756501832322780285 7700310283688187121042607)
        ·
          refine ⟨11550465425532280681563911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700310283688187121042607 11550465425532280681563911)
          ·
            refine ⟨17325698138298421022345867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11550465425532280681563911 17325698138298421022345867)
            ·
              refine ⟨25988547207447631533518801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17325698138298421022345867 25988547207447631533518801)
              ·
                refine ⟨19491410405585723650139101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25988547207447631533518801 19491410405585723650139101)
                ·
                  refine ⟨7309278902094646368802163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19491410405585723650139101 7309278902094646368802163)
                  ·
                    refine ⟨10963918353141969553203245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7309278902094646368802163 10963918353141969553203245)
                    ·
                      refine ⟨4111469382428238582451217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10963918353141969553203245 4111469382428238582451217)
                      ·
                        rfl

theorem cell23_8007058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_8007058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007058 prefixEnd_8007058 := by exact prefixLift 8007058
  have htrace : WordTrace (prefixWord ++ tailWord_8007058) baseStart_8007058 baseEnd_8007058 := by
    simpa [prefixWord, tailWord_8007058, baseEnd_8007058] using wordTrace_append hprefix tailTrace_8007058
  have hstable : (prefixWord ++ tailWord_8007058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007058).length < 2 ^ (prefixWord ++ tailWord_8007058).sum := by decide
  have hdescent : baseEnd_8007058 < baseStart_8007058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007108 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_8007108 : Nat := 118140960795 + 8007108 * 2 ^ 59
def prefixEnd_8007108 : Nat := 4983230072969 + 3 ^ 40 * 8007108 * 2
def baseEnd_8007108 : Nat := 1370498352153654462275329

theorem tailTrace_8007108 : CollatzResearch.WordTrace tailWord_8007108 prefixEnd_8007108 1370498352153654462275329 := by
  unfold tailWord_8007108
  simp only [CollatzResearch.WordTrace]
  refine ⟨146021610537811348009430989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194695480717081797345907985 146021610537811348009430989)
  ·
    refine ⟨54758103951679255503536621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146021610537811348009430989 54758103951679255503536621)
    ·
      refine ⟨20534288981879720813826233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54758103951679255503536621 20534288981879720813826233)
      ·
        refine ⟨15400716736409790610369675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20534288981879720813826233 15400716736409790610369675)
        ·
          refine ⟨23101075104614685915554513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15400716736409790610369675 23101075104614685915554513)
          ·
            refine ⟨17325806328461014436665885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23101075104614685915554513 17325806328461014436665885)
            ·
              refine ⟨6497177373172880413749707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17325806328461014436665885 6497177373172880413749707)
              ·
                refine ⟨9745766059759320620624561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497177373172880413749707 9745766059759320620624561)
                ·
                  refine ⟨7309324544819490465468421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9745766059759320620624561 7309324544819490465468421)
                  ·
                    refine ⟨1370498352153654462275329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7309324544819490465468421 1370498352153654462275329)
                    ·
                      rfl

theorem cell23_8007108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_8007108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007108 prefixEnd_8007108 := by exact prefixLift 8007108
  have htrace : WordTrace (prefixWord ++ tailWord_8007108) baseStart_8007108 baseEnd_8007108 := by
    simpa [prefixWord, tailWord_8007108, baseEnd_8007108] using wordTrace_append hprefix tailTrace_8007108
  have hstable : (prefixWord ++ tailWord_8007108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007108).length < 2 ^ (prefixWord ++ tailWord_8007108).sum := by decide
  have hdescent : baseEnd_8007108 < baseStart_8007108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007114 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_8007114 : Nat := 118140960795 + 8007114 * 2 ^ 59
def prefixEnd_8007114 : Nat := 4983230072969 + 3 ^ 40 * 8007114 * 2
def baseEnd_8007114 : Nat := 4111498137344890363350959

theorem tailTrace_8007114 : CollatzResearch.WordTrace tailWord_8007114 prefixEnd_8007114 4111498137344890363350959 := by
  unfold tailWord_8007114
  simp only [CollatzResearch.WordTrace]
  refine ⟨73010859978400239760895099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194695626609067306029053597 73010859978400239760895099)
  ·
    refine ⟨109516289967600359641342649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73010859978400239760895099 109516289967600359641342649)
    ·
      refine ⟨82137217475700269731006987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109516289967600359641342649 82137217475700269731006987)
      ·
        refine ⟨123205826213550404596510481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82137217475700269731006987 123205826213550404596510481)
        ·
          refine ⟨92404369660162803447382861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123205826213550404596510481 92404369660162803447382861)
          ·
            refine ⟨34651638622561051292768573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92404369660162803447382861 34651638622561051292768573)
            ·
              refine ⟨12994364483460394234788215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34651638622561051292768573 12994364483460394234788215)
              ·
                refine ⟨19491546725190591352182323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12994364483460394234788215 19491546725190591352182323)
                ·
                  refine ⟨29237320087785887028273485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19491546725190591352182323 29237320087785887028273485)
                  ·
                    refine ⟨10963995032919707635602557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29237320087785887028273485 10963995032919707635602557)
                    ·
                      refine ⟨4111498137344890363350959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10963995032919707635602557 4111498137344890363350959)
                      ·
                        rfl

theorem cell23_8007114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_8007114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007114 prefixEnd_8007114 := by exact prefixLift 8007114
  have htrace : WordTrace (prefixWord ++ tailWord_8007114) baseStart_8007114 baseEnd_8007114 := by
    simpa [prefixWord, tailWord_8007114, baseEnd_8007114] using wordTrace_append hprefix tailTrace_8007114
  have hstable : (prefixWord ++ tailWord_8007114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007114).length < 2 ^ (prefixWord ++ tailWord_8007114).sum := by decide
  have hdescent : baseEnd_8007114 < baseStart_8007114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007194 : List Nat := [3, 1, 1, 3, 1, 1, 1, 7, 5]
def baseStart_8007194 : Nat := 118140960795 + 8007194 * 2 ^ 59
def prefixEnd_8007194 : Nat := 4983230072969 + 3 ^ 40 * 8007194 * 2
def baseEnd_8007194 : Nat := 456837690644138894483399

theorem tailTrace_8007194 : CollatzResearch.WordTrace tailWord_8007194 prefixEnd_8007194 456837690644138894483399 := by
  unfold tailWord_8007194
  simp only [CollatzResearch.WordTrace]
  refine ⟨73011589438327783176623159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194697571835540755137661757 73011589438327783176623159)
  ·
    refine ⟨109517384157491674764934739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73011589438327783176623159 109517384157491674764934739)
    ·
      refine ⟨164276076236237512147402109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109517384157491674764934739 164276076236237512147402109)
      ·
        refine ⟨61603528588589067055275791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164276076236237512147402109 61603528588589067055275791)
        ·
          refine ⟨92405292882883600582913687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61603528588589067055275791 92405292882883600582913687)
          ·
            refine ⟨138607939324325400874370531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92405292882883600582913687 138607939324325400874370531)
            ·
              refine ⟨207911908986488101311555797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138607939324325400874370531 207911908986488101311555797)
              ·
                refine ⟨4872935366870814874489589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207911908986488101311555797 4872935366870814874489589)
                ·
                  refine ⟨456837690644138894483399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4872935366870814874489589 456837690644138894483399)
                  ·
                    rfl

theorem cell23_8007194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_8007194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007194 prefixEnd_8007194 := by exact prefixLift 8007194
  have htrace : WordTrace (prefixWord ++ tailWord_8007194) baseStart_8007194 baseEnd_8007194 := by
    simpa [prefixWord, tailWord_8007194, baseEnd_8007194] using wordTrace_append hprefix tailTrace_8007194
  have hstable : (prefixWord ++ tailWord_8007194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007194).length < 2 ^ (prefixWord ++ tailWord_8007194).sum := by decide
  have hdescent : baseEnd_8007194 < baseStart_8007194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007244 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_8007244 : Nat := 118140960795 + 8007244 * 2 ^ 59
def prefixEnd_8007244 : Nat := 4983230072969 + 3 ^ 40 * 8007244 * 2
def baseEnd_8007244 : Nat := 4111564889829974854725361

theorem tailTrace_8007244 : CollatzResearch.WordTrace tailWord_8007244 prefixEnd_8007244 4111564889829974854725361 := by
  unfold tailWord_8007244
  simp only [CollatzResearch.WordTrace]
  refine ⟨146024090701564995622906393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194698787602086660830541857 146024090701564995622906393)
  ·
    refine ⟨109518068026173746717179795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146024090701564995622906393 109518068026173746717179795)
    ·
      refine ⟨164277102039260620075769693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109518068026173746717179795 164277102039260620075769693)
      ·
        refine ⟨61603913264722732528413635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164277102039260620075769693 61603913264722732528413635)
        ·
          refine ⟨92405869897084098792620453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61603913264722732528413635 92405869897084098792620453)
          ·
            refine ⟨17326100605703268523616335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92405869897084098792620453 17326100605703268523616335)
            ·
              refine ⟨25989150908554902785424503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17326100605703268523616335 25989150908554902785424503)
              ·
                refine ⟨38983726362832354178136755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25989150908554902785424503 38983726362832354178136755)
                ·
                  refine ⟨58475589544248531267205133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38983726362832354178136755 58475589544248531267205133)
                  ·
                    refine ⟨21928346079093199225201925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58475589544248531267205133 21928346079093199225201925)
                    ·
                      refine ⟨4111564889829974854725361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21928346079093199225201925 4111564889829974854725361)
                      ·
                        rfl

theorem cell23_8007244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_8007244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007244 prefixEnd_8007244 := by exact prefixLift 8007244
  have htrace : WordTrace (prefixWord ++ tailWord_8007244) baseStart_8007244 baseEnd_8007244 := by
    simpa [prefixWord, tailWord_8007244, baseEnd_8007244] using wordTrace_append hprefix tailTrace_8007244
  have hstable : (prefixWord ++ tailWord_8007244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007244).length < 2 ^ (prefixWord ++ tailWord_8007244).sum := by decide
  have hdescent : baseEnd_8007244 < baseStart_8007244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007257 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_8007257 : Nat := 118140960795 + 8007257 * 2 ^ 59
def prefixEnd_8007257 : Nat := 4983230072969 + 3 ^ 40 * 8007257 * 2
def baseEnd_8007257 : Nat := 4111571565078483303862801

theorem tailTrace_8007257 : CollatzResearch.WordTrace tailWord_8007257 prefixEnd_8007257 4111571565078483303862801 := by
  unfold tailWord_8007257
  simp only [CollatzResearch.WordTrace]
  refine ⟨292048655552082894466036025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194699103701388596310690683 292048655552082894466036025)
  ·
    refine ⟨219036491664062170849527019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292048655552082894466036025 219036491664062170849527019)
    ·
      refine ⟨328554737496093256274290529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219036491664062170849527019 328554737496093256274290529)
      ·
        refine ⟨246416053122069942205717897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328554737496093256274290529 246416053122069942205717897)
        ·
          refine ⟨184812039841552456654288423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246416053122069942205717897 184812039841552456654288423)
          ·
            refine ⟨277218059762328684981432635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184812039841552456654288423 277218059762328684981432635)
            ·
              refine ⟨415827089643493027472148953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277218059762328684981432635 415827089643493027472148953)
              ·
                refine ⟨311870317232619770604111715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415827089643493027472148953 311870317232619770604111715)
                ·
                  refine ⟨467805475848929655906167573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311870317232619770604111715 467805475848929655906167573)
                  ·
                    refine ⟨21928381680418577620601605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 467805475848929655906167573 21928381680418577620601605)
                    ·
                      refine ⟨4111571565078483303862801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21928381680418577620601605 4111571565078483303862801)
                      ·
                        rfl

theorem cell23_8007257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_8007257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007257 prefixEnd_8007257 := by exact prefixLift 8007257
  have htrace : WordTrace (prefixWord ++ tailWord_8007257) baseStart_8007257 baseEnd_8007257 := by
    simpa [prefixWord, tailWord_8007257, baseEnd_8007257] using wordTrace_append hprefix tailTrace_8007257
  have hstable : (prefixWord ++ tailWord_8007257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007257).length < 2 ^ (prefixWord ++ tailWord_8007257).sum := by decide
  have hdescent : baseEnd_8007257 < baseStart_8007257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007264 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 3]
def baseStart_8007264 : Nat := 118140960795 + 8007264 * 2 ^ 59
def prefixEnd_8007264 : Nat := 4983230072969 + 3 ^ 40 * 8007264 * 2
def baseEnd_8007264 : Nat := 4111575159443064776475269

theorem tailTrace_8007264 : CollatzResearch.WordTrace tailWord_8007264 prefixEnd_8007264 4111575159443064776475269 := by
  unfold tailWord_8007264
  simp only [CollatzResearch.WordTrace]
  refine ⟨146024455431528767330770423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194699273908705023107693897 146024455431528767330770423)
  ·
    refine ⟨219036683147293150996155635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146024455431528767330770423 219036683147293150996155635)
    ·
      refine ⟨328555024720939726494233453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219036683147293150996155635 328555024720939726494233453)
      ·
        refine ⟨123208134270352397435337545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328555024720939726494233453 123208134270352397435337545)
        ·
          refine ⟨92406100702764298076503159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123208134270352397435337545 92406100702764298076503159)
          ·
            refine ⟨138609151054146447114754739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92406100702764298076503159 138609151054146447114754739)
            ·
              refine ⟨207913726581219670672132109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138609151054146447114754739 207913726581219670672132109)
              ·
                refine ⟨77967647467957376502049541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207913726581219670672132109 77967647467957376502049541)
                ·
                  refine ⟨14618933900242008094134289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77967647467957376502049541 14618933900242008094134289)
                  ·
                    refine ⟨10964200425181506070600717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14618933900242008094134289 10964200425181506070600717)
                    ·
                      refine ⟨4111575159443064776475269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10964200425181506070600717 4111575159443064776475269)
                      ·
                        rfl

theorem cell23_8007264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_8007264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007264 prefixEnd_8007264 := by exact prefixLift 8007264
  have htrace : WordTrace (prefixWord ++ tailWord_8007264) baseStart_8007264 baseEnd_8007264 := by
    simpa [prefixWord, tailWord_8007264, baseEnd_8007264] using wordTrace_append hprefix tailTrace_8007264
  have hstable : (prefixWord ++ tailWord_8007264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007264).length < 2 ^ (prefixWord ++ tailWord_8007264).sum := by decide
  have hdescent : baseEnd_8007264 < baseStart_8007264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007287 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_8007287 : Nat := 118140960795 + 8007287 * 2 ^ 59
def prefixEnd_8007287 : Nat := 4983230072969 + 3 ^ 40 * 8007287 * 2
def baseEnd_8007287 : Nat := 4111586969498118186487663

theorem tailTrace_8007287 : CollatzResearch.WordTrace tailWord_8007287 prefixEnd_8007287 4111586969498118186487663 := by
  unfold tailWord_8007287
  simp only [CollatzResearch.WordTrace]
  refine ⟨292049749741974209589628115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194699833161316139726418743 292049749741974209589628115)
  ·
    refine ⟨438074624612961314384442173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292049749741974209589628115 438074624612961314384442173)
    ·
      refine ⟨164277984229860492894165815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438074624612961314384442173 164277984229860492894165815)
      ·
        refine ⟨246416976344790739341248723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164277984229860492894165815 246416976344790739341248723)
        ·
          refine ⟨369625464517186109011873085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246416976344790739341248723 369625464517186109011873085)
          ·
            refine ⟨138609549193944790879452407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369625464517186109011873085 138609549193944790879452407)
            ·
              refine ⟨207914323790917186319178611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138609549193944790879452407 207914323790917186319178611)
              ·
                refine ⟨311871485686375779478767917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207914323790917186319178611 311871485686375779478767917)
                ·
                  refine ⟨116951807132390917304537969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311871485686375779478767917 116951807132390917304537969)
                  ·
                    refine ⟨87713855349293187978403477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116951807132390917304537969 87713855349293187978403477)
                    ·
                      refine ⟨4111586969498118186487663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87713855349293187978403477 4111586969498118186487663)
                      ·
                        rfl

theorem cell23_8007287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_8007287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007287 prefixEnd_8007287 := by exact prefixLift 8007287
  have htrace : WordTrace (prefixWord ++ tailWord_8007287) baseStart_8007287 baseEnd_8007287 := by
    simpa [prefixWord, tailWord_8007287, baseEnd_8007287] using wordTrace_append hprefix tailTrace_8007287
  have hstable : (prefixWord ++ tailWord_8007287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007287).length < 2 ^ (prefixWord ++ tailWord_8007287).sum := by decide
  have hdescent : baseEnd_8007287 < baseStart_8007287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007328 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 3, 1, 3]
def baseStart_8007328 : Nat := 118140960795 + 8007328 * 2 ^ 59
def prefixEnd_8007328 : Nat := 4983230072969 + 3 ^ 40 * 8007328 * 2
def baseEnd_8007328 : Nat := 4111608022204952526074975

theorem tailTrace_8007328 : CollatzResearch.WordTrace tailWord_8007328 prefixEnd_8007328 4111608022204952526074975 := by
  unfold tailWord_8007328
  simp only [CollatzResearch.WordTrace]
  refine ⟨146025622567412836795935319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194700830089883782394580425 146025622567412836795935319)
  ·
    refine ⟨219038433851119255193902979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146025622567412836795935319 219038433851119255193902979)
    ·
      refine ⟨328557650776678882790854469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219038433851119255193902979 328557650776678882790854469)
      ·
        refine ⟨61604559520627290523285213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328557650776678882790854469 61604559520627290523285213)
        ·
          refine ⟨23101709820235233946231955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61604559520627290523285213 23101709820235233946231955)
          ·
            refine ⟨34652564730352850919347933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23101709820235233946231955 34652564730352850919347933)
            ·
              refine ⟨12994711773882319094755475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34652564730352850919347933 12994711773882319094755475)
              ·
                refine ⟨19492067660823478642133213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12994711773882319094755475 19492067660823478642133213)
                ·
                  refine ⟨7309525372808804490799955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19492067660823478642133213 7309525372808804490799955)
                  ·
                    refine ⟨10964288059213206736199933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7309525372808804490799955 10964288059213206736199933)
                    ·
                      refine ⟨4111608022204952526074975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10964288059213206736199933 4111608022204952526074975)
                      ·
                        rfl

theorem cell23_8007328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_8007328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007328 prefixEnd_8007328 := by exact prefixLift 8007328
  have htrace : WordTrace (prefixWord ++ tailWord_8007328) baseStart_8007328 baseEnd_8007328 := by
    simpa [prefixWord, tailWord_8007328, baseEnd_8007328] using wordTrace_append hprefix tailTrace_8007328
  have hstable : (prefixWord ++ tailWord_8007328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007328).length < 2 ^ (prefixWord ++ tailWord_8007328).sum := by decide
  have hdescent : baseEnd_8007328 < baseStart_8007328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007351 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_8007351 : Nat := 118140960795 + 8007351 * 2 ^ 59
def prefixEnd_8007351 : Nat := 4983230072969 + 3 ^ 40 * 8007351 * 2
def baseEnd_8007351 : Nat := 4111619832260005936087369

theorem tailTrace_8007351 : CollatzResearch.WordTrace tailWord_8007351 prefixEnd_8007351 4111619832260005936087369 := by
  unfold tailWord_8007351
  simp only [CollatzResearch.WordTrace]
  refine ⟨292052084013742348519957907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194701389342494899013305271 292052084013742348519957907)
  ·
    refine ⟨438078126020613522779936861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292052084013742348519957907 438078126020613522779936861)
    ·
      refine ⟨164279297257730071042476323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438078126020613522779936861 164279297257730071042476323)
      ·
        refine ⟨246418945886595106563714485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164279297257730071042476323 246418945886595106563714485)
        ·
          refine ⟨23101776176868291240348233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246418945886595106563714485 23101776176868291240348233)
          ·
            refine ⟨17326332132651218430261175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23101776176868291240348233 17326332132651218430261175)
            ·
              refine ⟨25989498198976827645391763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17326332132651218430261175 25989498198976827645391763)
              ·
                refine ⟨38984247298465241468087645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25989498198976827645391763 38984247298465241468087645)
                ·
                  refine ⟨14619092736924465550532867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38984247298465241468087645 14619092736924465550532867)
                  ·
                    refine ⟨21928639105386698325799301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14619092736924465550532867 21928639105386698325799301)
                    ·
                      refine ⟨4111619832260005936087369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21928639105386698325799301 4111619832260005936087369)
                      ·
                        rfl

theorem cell23_8007351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_8007351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007351 prefixEnd_8007351 := by exact prefixLift 8007351
  have htrace : WordTrace (prefixWord ++ tailWord_8007351) baseStart_8007351 baseEnd_8007351 := by
    simpa [prefixWord, tailWord_8007351, baseEnd_8007351] using wordTrace_append hprefix tailTrace_8007351
  have hstable : (prefixWord ++ tailWord_8007351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007351).length < 2 ^ (prefixWord ++ tailWord_8007351).sum := by decide
  have hdescent : baseEnd_8007351 < baseStart_8007351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007368 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_8007368 : Nat := 118140960795 + 8007368 * 2 ^ 59
def prefixEnd_8007368 : Nat := 4983230072969 + 3 ^ 40 * 8007368 * 2
def baseEnd_8007368 : Nat := 4111628561431132369574791

theorem tailTrace_8007368 : CollatzResearch.WordTrace tailWord_8007368 prefixEnd_8007368 4111628561431132369574791 := by
  unfold tailWord_8007368
  simp only [CollatzResearch.WordTrace]
  refine ⟨146026352027340380211663379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194701802703120506948884505 146026352027340380211663379)
  ·
    refine ⟨219039528041010570317495069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146026352027340380211663379 219039528041010570317495069)
    ·
      refine ⟨82139823015378963869060651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219039528041010570317495069 82139823015378963869060651)
      ·
        refine ⟨123209734523068445803590977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82139823015378963869060651 123209734523068445803590977)
        ·
          refine ⟨92407300892301334352693233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123209734523068445803590977 92407300892301334352693233)
          ·
            refine ⟨69305475669226000764519925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92407300892301334352693233 69305475669226000764519925)
            ·
              refine ⟨6497388343989937571673743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69305475669226000764519925 6497388343989937571673743)
              ·
                refine ⟨9746082515984906357510615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497388343989937571673743 9746082515984906357510615)
                ·
                  refine ⟨14619123773977359536265923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9746082515984906357510615 14619123773977359536265923)
                  ·
                    refine ⟨21928685660966039304398885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14619123773977359536265923 21928685660966039304398885)
                    ·
                      refine ⟨4111628561431132369574791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21928685660966039304398885 4111628561431132369574791)
                      ·
                        rfl

theorem cell23_8007368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_8007368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007368 prefixEnd_8007368 := by exact prefixLift 8007368
  have htrace : WordTrace (prefixWord ++ tailWord_8007368) baseStart_8007368 baseEnd_8007368 := by
    simpa [prefixWord, tailWord_8007368, baseEnd_8007368] using wordTrace_append hprefix tailTrace_8007368
  have hstable : (prefixWord ++ tailWord_8007368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007368).length < 2 ^ (prefixWord ++ tailWord_8007368).sum := by decide
  have hdescent : baseEnd_8007368 < baseStart_8007368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007371 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 3]
def baseStart_8007371 : Nat := 118140960795 + 8007371 * 2 ^ 59
def prefixEnd_8007371 : Nat := 4983230072969 + 3 ^ 40 * 8007371 * 2
def baseEnd_8007371 : Nat := 4111630101873095857837277

theorem tailTrace_8007371 : CollatzResearch.WordTrace tailWord_8007371 prefixEnd_8007371 4111630101873095857837277 := by
  unfold tailWord_8007371
  simp only [CollatzResearch.WordTrace]
  refine ⟨292052813473669891935685967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194701875649113261290457311 292052813473669891935685967)
  ·
    refine ⟨438079220210504837903528951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292052813473669891935685967 438079220210504837903528951)
    ·
      refine ⟨657118830315757256855293427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438079220210504837903528951 657118830315757256855293427)
      ·
        refine ⟨985678245473635885282940141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657118830315757256855293427 985678245473635885282940141)
        ·
          refine ⟨369629342052613456981102553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 985678245473635885282940141 369629342052613456981102553)
          ·
            refine ⟨277222006539460092735826915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369629342052613456981102553 277222006539460092735826915)
            ·
              refine ⟨415833009809190139103740373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277222006539460092735826915 415833009809190139103740373)
              ·
                refine ⟨9746086167402893885243915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 415833009809190139103740373 9746086167402893885243915)
                ·
                  refine ⟨14619129251104340827865873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9746086167402893885243915 14619129251104340827865873)
                  ·
                    refine ⟨10964346938328255620899405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14619129251104340827865873 10964346938328255620899405)
                    ·
                      refine ⟨4111630101873095857837277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10964346938328255620899405 4111630101873095857837277)
                      ·
                        rfl

theorem cell23_8007371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 3].length) (baseStart_8007371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007371 prefixEnd_8007371 := by exact prefixLift 8007371
  have htrace : WordTrace (prefixWord ++ tailWord_8007371) baseStart_8007371 baseEnd_8007371 := by
    simpa [prefixWord, tailWord_8007371, baseEnd_8007371] using wordTrace_append hprefix tailTrace_8007371
  have hstable : (prefixWord ++ tailWord_8007371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007371).length < 2 ^ (prefixWord ++ tailWord_8007371).sum := by decide
  have hdescent : baseEnd_8007371 < baseStart_8007371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007378 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_8007378 : Nat := 118140960795 + 8007378 * 2 ^ 59
def prefixEnd_8007378 : Nat := 4983230072969 + 3 ^ 40 * 8007378 * 2
def baseEnd_8007378 : Nat := 1370544565412559110149915

theorem tailTrace_8007378 : CollatzResearch.WordTrace tailWord_8007378 prefixEnd_8007378 1370544565412559110149915 := by
  unfold tailWord_8007378
  simp only [CollatzResearch.WordTrace]
  refine ⟨73013267196161133032797697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194702045856429688087460525 73013267196161133032797697)
  ·
    refine ⟨54759950397120849774598273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73013267196161133032797697 54759950397120849774598273)
    ·
      refine ⟨41069962797840637330948705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54759950397120849774598273 41069962797840637330948705)
      ·
        refine ⟨30802472098380477998211529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41069962797840637330948705 30802472098380477998211529)
        ·
          refine ⟨23101854073785358498658647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30802472098380477998211529 23101854073785358498658647)
          ·
            refine ⟨34652781110678037747987971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23101854073785358498658647 34652781110678037747987971)
            ·
              refine ⟨51979171666017056621981957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34652781110678037747987971 51979171666017056621981957)
              ·
                refine ⟨9746094687378198116621617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51979171666017056621981957 9746094687378198116621617)
                ·
                  refine ⟨7309571015533648587466213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9746094687378198116621617 7309571015533648587466213)
                  ·
                    refine ⟨1370544565412559110149915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7309571015533648587466213 1370544565412559110149915)
                    ·
                      rfl

theorem cell23_8007378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_8007378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007378 prefixEnd_8007378 := by exact prefixLift 8007378
  have htrace : WordTrace (prefixWord ++ tailWord_8007378) baseStart_8007378 baseEnd_8007378 := by
    simpa [prefixWord, tailWord_8007378, baseEnd_8007378] using wordTrace_append hprefix tailTrace_8007378
  have hstable : (prefixWord ++ tailWord_8007378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007378).length < 2 ^ (prefixWord ++ tailWord_8007378).sum := by decide
  have hdescent : baseEnd_8007378 < baseStart_8007378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007401 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 3]
def baseStart_8007401 : Nat := 118140960795 + 8007401 * 2 ^ 59
def prefixEnd_8007401 : Nat := 4983230072969 + 3 ^ 40 * 8007401 * 2
def baseEnd_8007401 : Nat := 4111645506292730740462139

theorem tailTrace_8007401 : CollatzResearch.WordTrace tailWord_8007401 prefixEnd_8007401 4111645506292730740462139 := by
  unfold tailWord_8007401
  simp only [CollatzResearch.WordTrace]
  refine ⟨292053907663561207059278057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194702605109040804706185371 292053907663561207059278057)
  ·
    refine ⟨219040430747670905294458543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292053907663561207059278057 219040430747670905294458543)
    ·
      refine ⟨328560646121506357941687815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219040430747670905294458543 328560646121506357941687815)
      ·
        refine ⟨492840969182259536912531723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328560646121506357941687815 492840969182259536912531723)
        ·
          refine ⟨739261453773389305368797585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492840969182259536912531723 739261453773389305368797585)
          ·
            refine ⟨554446090330041979026598189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739261453773389305368797585 554446090330041979026598189)
            ·
              refine ⟨207917283873765742134974321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554446090330041979026598189 207917283873765742134974321)
              ·
                refine ⟨155937962905324306601230741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207917283873765742134974321 155937962905324306601230741)
                ·
                  refine ⟨7309592011187076871932691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155937962905324306601230741 7309592011187076871932691)
                  ·
                    refine ⟨10964388016780615307899037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7309592011187076871932691 10964388016780615307899037)
                    ·
                      refine ⟨4111645506292730740462139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10964388016780615307899037 4111645506292730740462139)
                      ·
                        rfl

theorem cell23_8007401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 3].length) (baseStart_8007401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007401 prefixEnd_8007401 := by exact prefixLift 8007401
  have htrace : WordTrace (prefixWord ++ tailWord_8007401) baseStart_8007401 baseEnd_8007401 := by
    simpa [prefixWord, tailWord_8007401, baseEnd_8007401] using wordTrace_append hprefix tailTrace_8007401
  have hstable : (prefixWord ++ tailWord_8007401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007401).length < 2 ^ (prefixWord ++ tailWord_8007401).sum := by decide
  have hdescent : baseEnd_8007401 < baseStart_8007401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007424 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_8007424 : Nat := 118140960795 + 8007424 * 2 ^ 59
def prefixEnd_8007424 : Nat := 4983230072969 + 3 ^ 40 * 8007424 * 2
def baseEnd_8007424 : Nat := 4111657316347784150474533

theorem tailTrace_8007424 : CollatzResearch.WordTrace tailWord_8007424 prefixEnd_8007424 4111657316347784150474533 := by
  unfold tailWord_8007424
  simp only [CollatzResearch.WordTrace]
  refine ⟨146027373271238940993682663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194703164361651921324910217 146027373271238940993682663)
  ·
    refine ⟨219041059906858411490523995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146027373271238940993682663 219041059906858411490523995)
    ·
      refine ⟨328561589860287617235785993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219041059906858411490523995 328561589860287617235785993)
      ·
        refine ⟨246421192395215712926839495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328561589860287617235785993 246421192395215712926839495)
        ·
          refine ⟨369631788592823569390259243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246421192395215712926839495 369631788592823569390259243)
          ·
            refine ⟨554447682889235354085388865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369631788592823569390259243 554447682889235354085388865)
            ·
              refine ⟨415835762166926515564041649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554447682889235354085388865 415835762166926515564041649)
              ·
                refine ⟨311876821625194886673031237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415835762166926515564041649 311876821625194886673031237)
                ·
                  refine ⟨58476904054724041251193357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311876821625194886673031237 58476904054724041251193357)
                  ·
                    refine ⟨21928839020521515469197509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58476904054724041251193357 21928839020521515469197509)
                    ·
                      refine ⟨4111657316347784150474533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21928839020521515469197509 4111657316347784150474533)
                      ·
                        rfl

theorem cell23_8007424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_8007424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007424 prefixEnd_8007424 := by exact prefixLift 8007424
  have htrace : WordTrace (prefixWord ++ tailWord_8007424) baseStart_8007424 baseEnd_8007424 := by
    simpa [prefixWord, tailWord_8007424, baseEnd_8007424] using wordTrace_append hprefix tailTrace_8007424
  have hstable : (prefixWord ++ tailWord_8007424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007424).length < 2 ^ (prefixWord ++ tailWord_8007424).sum := by decide
  have hdescent : baseEnd_8007424 < baseStart_8007424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007478 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_8007478 : Nat := 118140960795 + 8007478 * 2 ^ 59
def prefixEnd_8007478 : Nat := 4983230072969 + 3 ^ 40 * 8007478 * 2
def baseEnd_8007478 : Nat := 4111685044303126939199285

theorem tailTrace_8007478 : CollatzResearch.WordTrace tailWord_8007478 prefixEnd_8007478 4111685044303126939199285 := by
  unfold tailWord_8007478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18253544755267640575614443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194704477389521499473220725 18253544755267640575614443)
  ·
    refine ⟨27380317132901460863421665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18253544755267640575614443 27380317132901460863421665)
    ·
      refine ⟨20535237849676095647566249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27380317132901460863421665 20535237849676095647566249)
      ·
        refine ⟨15401428387257071735674687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20535237849676095647566249 15401428387257071735674687)
        ·
          refine ⟨23102142580885607603512031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15401428387257071735674687 23102142580885607603512031)
          ·
            refine ⟨34653213871328411405268047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23102142580885607603512031 34653213871328411405268047)
            ·
              refine ⟨51979820806992617107902071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34653213871328411405268047 51979820806992617107902071)
              ·
                refine ⟨77969731210488925661853107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51979820806992617107902071 77969731210488925661853107)
                ·
                  refine ⟨116954596815733388492779661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77969731210488925661853107 116954596815733388492779661)
                  ·
                    refine ⟨43857973805900020684792373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116954596815733388492779661 43857973805900020684792373)
                    ·
                      refine ⟨4111685044303126939199285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43857973805900020684792373 4111685044303126939199285)
                      ·
                        rfl

theorem cell23_8007478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_8007478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007478 prefixEnd_8007478 := by exact prefixLift 8007478
  have htrace : WordTrace (prefixWord ++ tailWord_8007478) baseStart_8007478 baseEnd_8007478 := by
    simpa [prefixWord, tailWord_8007478, baseEnd_8007478] using wordTrace_append hprefix tailTrace_8007478
  have hstable : (prefixWord ++ tailWord_8007478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007478).length < 2 ^ (prefixWord ++ tailWord_8007478).sum := by decide
  have hdescent : baseEnd_8007478 < baseStart_8007478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007509 : List Nat := [1, 3, 2, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_8007509 : Nat := 118140960795 + 8007509 * 2 ^ 59
def prefixEnd_8007509 : Nat := 4983230072969 + 3 ^ 40 * 8007509 * 2
def baseEnd_8007509 : Nat := 4111700962203416317911643

theorem tailTrace_8007509 : CollatzResearch.WordTrace tailWord_8007509 prefixEnd_8007509 4111700962203416317911643 := by
  unfold tailWord_8007509
  simp only [CollatzResearch.WordTrace]
  refine ⟨292057846747169941504209581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194705231164779961002806387 292057846747169941504209581)
  ·
    refine ⟨109521692530188728064078593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292057846747169941504209581 109521692530188728064078593)
    ·
      refine ⟨82141269397641546048058945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109521692530188728064078593 82141269397641546048058945)
      ·
        refine ⟨61605952048231159536044209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82141269397641546048058945 61605952048231159536044209)
        ·
          refine ⟨46204464036173369652033157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61605952048231159536044209 46204464036173369652033157)
          ·
            refine ⟨8663337006782506809756217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46204464036173369652033157 8663337006782506809756217)
            ·
              refine ⟨6497502755086880107317163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8663337006782506809756217 6497502755086880107317163)
              ·
                refine ⟨9746254132630320160975745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497502755086880107317163 9746254132630320160975745)
                ·
                  refine ⟨7309690599472740120731809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9746254132630320160975745 7309690599472740120731809)
                  ·
                    refine ⟨5482267949604555090548857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7309690599472740120731809 5482267949604555090548857)
                    ·
                      refine ⟨4111700962203416317911643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482267949604555090548857 4111700962203416317911643)
                      ·
                        rfl

theorem cell23_8007509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_8007509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007509 prefixEnd_8007509 := by exact prefixLift 8007509
  have htrace : WordTrace (prefixWord ++ tailWord_8007509) baseStart_8007509 baseEnd_8007509 := by
    simpa [prefixWord, tailWord_8007509, baseEnd_8007509] using wordTrace_append hprefix tailTrace_8007509
  have hstable : (prefixWord ++ tailWord_8007509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007509).length < 2 ^ (prefixWord ++ tailWord_8007509).sum := by decide
  have hdescent : baseEnd_8007509 < baseStart_8007509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007528 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 2, 5]
def baseStart_8007528 : Nat := 118140960795 + 8007528 * 2 ^ 59
def prefixEnd_8007528 : Nat := 4983230072969 + 3 ^ 40 * 8007528 * 2
def baseEnd_8007528 : Nat := 1370570239445283914524685

theorem tailTrace_8007528 : CollatzResearch.WordTrace tailWord_8007528 prefixEnd_8007528 1370570239445283914524685 := by
  unfold tailWord_8007528
  simp only [CollatzResearch.WordTrace]
  refine ⟨146029269867050553874575619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194705693156067405166100825 146029269867050553874575619)
  ·
    refine ⟨219043904800575830811863429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146029269867050553874575619 219043904800575830811863429)
    ·
      refine ⟨41070732150107968277224393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219043904800575830811863429 41070732150107968277224393)
      ·
        refine ⟨30803049112580976207918295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41070732150107968277224393 30803049112580976207918295)
        ·
          refine ⟨46204573668871464311877443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30803049112580976207918295 46204573668871464311877443)
          ·
            refine ⟨69306860503307196467816165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46204573668871464311877443 69306860503307196467816165)
            ·
              refine ⟨12995036344370099337715531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69306860503307196467816165 12995036344370099337715531)
              ·
                refine ⟨19492554516555149006573297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12995036344370099337715531 19492554516555149006573297)
                ·
                  refine ⟨14619415887416361754929973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19492554516555149006573297 14619415887416361754929973)
                  ·
                    refine ⟨1370570239445283914524685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14619415887416361754929973 1370570239445283914524685)
                    ·
                      rfl

theorem cell23_8007528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_8007528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007528 prefixEnd_8007528 := by exact prefixLift 8007528
  have htrace : WordTrace (prefixWord ++ tailWord_8007528) baseStart_8007528 baseEnd_8007528 := by
    simpa [prefixWord, tailWord_8007528, baseEnd_8007528] using wordTrace_append hprefix tailTrace_8007528
  have hstable : (prefixWord ++ tailWord_8007528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007528).length < 2 ^ (prefixWord ++ tailWord_8007528).sum := by decide
  have hdescent : baseEnd_8007528 < baseStart_8007528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007551 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 3]
def baseStart_8007551 : Nat := 118140960795 + 8007551 * 2 ^ 59
def prefixEnd_8007551 : Nat := 4983230072969 + 3 ^ 40 * 8007551 * 2
def baseEnd_8007551 : Nat := 4111722528390905153586449

theorem tailTrace_8007551 : CollatzResearch.WordTrace tailWord_8007551 prefixEnd_8007551 4111722528390905153586449 := by
  unfold tailWord_8007551
  simp only [CollatzResearch.WordTrace]
  refine ⟨292059378613017782677238507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194706252408678521784825671 292059378613017782677238507)
  ·
    refine ⟨438089067919526674015857761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292059378613017782677238507 438089067919526674015857761)
    ·
      refine ⟨328566800939645005511893321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438089067919526674015857761 328566800939645005511893321)
      ·
        refine ⟨246425100704733754133919991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328566800939645005511893321 246425100704733754133919991)
        ·
          refine ⟨369637651057100631200879987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246425100704733754133919991 369637651057100631200879987)
          ·
            refine ⟨554456476585650946801319981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369637651057100631200879987 554456476585650946801319981)
            ·
              refine ⟨207921178719619105050494993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554456476585650946801319981 207921178719619105050494993)
              ·
                refine ⟨155940884039714328787871245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207921178719619105050494993 155940884039714328787871245)
                ·
                  refine ⟨58477831514892873295451717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155940884039714328787871245 58477831514892873295451717)
                  ·
                    refine ⟨10964593409042413742897197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58477831514892873295451717 10964593409042413742897197)
                    ·
                      refine ⟨4111722528390905153586449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10964593409042413742897197 4111722528390905153586449)
                      ·
                        rfl

theorem cell23_8007551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_8007551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007551 prefixEnd_8007551 := by exact prefixLift 8007551
  have htrace : WordTrace (prefixWord ++ tailWord_8007551) baseStart_8007551 baseEnd_8007551 := by
    simpa [prefixWord, tailWord_8007551, baseEnd_8007551] using wordTrace_append hprefix tailTrace_8007551
  have hstable : (prefixWord ++ tailWord_8007551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007551).length < 2 ^ (prefixWord ++ tailWord_8007551).sum := by decide
  have hdescent : baseEnd_8007551 < baseStart_8007551 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007582 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_8007582 : Nat := 118140960795 + 8007582 * 2 ^ 59
def prefixEnd_8007582 : Nat := 4983230072969 + 3 ^ 40 * 8007582 * 2
def baseEnd_8007582 : Nat := 4111738446291194532298807

theorem tailTrace_8007582 : CollatzResearch.WordTrace tailWord_8007582 prefixEnd_8007582 4111738446291194532298807 := by
  unfold tailWord_8007582
  simp only [CollatzResearch.WordTrace]
  refine ⟨36507563659488184371452125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194707006183936983314411333 36507563659488184371452125)
  ·
    refine ⟨13690336372308069139294547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36507563659488184371452125 13690336372308069139294547)
    ·
      refine ⟨20535504558462103708941821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13690336372308069139294547 20535504558462103708941821)
      ·
        refine ⟨7700814209423288890853183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20535504558462103708941821 7700814209423288890853183)
        ·
          refine ⟨11551221314134933336279775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700814209423288890853183 11551221314134933336279775)
          ·
            refine ⟨17326831971202400004419663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551221314134933336279775 17326831971202400004419663)
            ·
              refine ⟨25990247956803600006629495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17326831971202400004419663 25990247956803600006629495)
              ·
                refine ⟨38985371935205400009944243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25990247956803600006629495 38985371935205400009944243)
                ·
                  refine ⟨58478057902808100014916365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38985371935205400009944243 58478057902808100014916365)
                  ·
                    refine ⟨21929271713553037505593637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58478057902808100014916365 21929271713553037505593637)
                    ·
                      refine ⟨4111738446291194532298807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21929271713553037505593637 4111738446291194532298807)
                      ·
                        rfl

theorem cell23_8007582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_8007582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007582 prefixEnd_8007582 := by exact prefixLift 8007582
  have htrace : WordTrace (prefixWord ++ tailWord_8007582) baseStart_8007582 baseEnd_8007582 := by
    simpa [prefixWord, tailWord_8007582, baseEnd_8007582] using wordTrace_append hprefix tailTrace_8007582
  have hstable : (prefixWord ++ tailWord_8007582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007582).length < 2 ^ (prefixWord ++ tailWord_8007582).sum := by decide
  have hdescent : baseEnd_8007582 < baseStart_8007582 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007585 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_8007585 : Nat := 118140960795 + 8007585 * 2 ^ 59
def prefixEnd_8007585 : Nat := 4983230072969 + 3 ^ 40 * 8007585 * 2
def baseEnd_8007585 : Nat := 4111739986733158020561293

theorem tailTrace_8007585 : CollatzResearch.WordTrace tailWord_8007585 prefixEnd_8007585 4111739986733158020561293 := by
  unfold tailWord_8007585
  simp only [CollatzResearch.WordTrace]
  refine ⟨292060618694894606483976209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194707079129929737655984139 292060618694894606483976209)
  ·
    refine ⟨219045464021170954862982157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292060618694894606483976209 219045464021170954862982157)
    ·
      refine ⟨82142049007939108073618309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219045464021170954862982157 82142049007939108073618309)
      ·
        refine ⟨15401634188988582763803433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82142049007939108073618309 15401634188988582763803433)
        ·
          refine ⟨11551225641741437072852575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15401634188988582763803433 11551225641741437072852575)
          ·
            refine ⟨17326838462612155609278863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551225641741437072852575 17326838462612155609278863)
            ·
              refine ⟨25990257693918233413918295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17326838462612155609278863 25990257693918233413918295)
              ·
                refine ⟨38985386540877350120877443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25990257693918233413918295 38985386540877350120877443)
                ·
                  refine ⟨58478079811316025181316165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38985386540877350120877443 58478079811316025181316165)
                  ·
                    refine ⟨10964639964621754721496781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58478079811316025181316165 10964639964621754721496781)
                    ·
                      refine ⟨4111739986733158020561293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10964639964621754721496781 4111739986733158020561293)
                      ·
                        rfl

theorem cell23_8007585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_8007585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007585 prefixEnd_8007585 := by exact prefixLift 8007585
  have htrace : WordTrace (prefixWord ++ tailWord_8007585) baseStart_8007585 baseEnd_8007585 := by
    simpa [prefixWord, tailWord_8007585, baseEnd_8007585] using wordTrace_append hprefix tailTrace_8007585
  have hstable : (prefixWord ++ tailWord_8007585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007585).length < 2 ^ (prefixWord ++ tailWord_8007585).sum := by decide
  have hdescent : baseEnd_8007585 < baseStart_8007585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007605 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 6]
def baseStart_8007605 : Nat := 118140960795 + 8007605 * 2 ^ 59
def prefixEnd_8007605 : Nat := 4983230072969 + 3 ^ 40 * 8007605 * 2
def baseEnd_8007605 : Nat := 456861139594027549145689

theorem tailTrace_8007605 : CollatzResearch.WordTrace tailWord_8007605 prefixEnd_8007605 456861139594027549145689 := by
  unfold tailWord_8007605
  simp only [CollatzResearch.WordTrace]
  refine ⟨292061348154822149899704269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194707565436548099933136179 292061348154822149899704269)
  ·
    refine ⟨109523005558058306212389101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292061348154822149899704269 109523005558058306212389101)
    ·
      refine ⟨41071127084271864829645913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109523005558058306212389101 41071127084271864829645913)
      ·
        refine ⟨30803345313203898622234435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41071127084271864829645913 30803345313203898622234435)
        ·
          refine ⟨46205017969805847933351653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30803345313203898622234435 46205017969805847933351653)
          ·
            refine ⟨8663440869338596487503435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46205017969805847933351653 8663440869338596487503435)
            ·
              refine ⟨12995161304007894731255153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663440869338596487503435 12995161304007894731255153)
              ·
                refine ⟨9746370978005921048441365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12995161304007894731255153 9746370978005921048441365)
                ·
                  refine ⟨456861139594027549145689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9746370978005921048441365 456861139594027549145689)
                  ·
                    rfl

theorem cell23_8007605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_8007605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007605 prefixEnd_8007605 := by exact prefixLift 8007605
  have htrace : WordTrace (prefixWord ++ tailWord_8007605) baseStart_8007605 baseEnd_8007605 := by
    simpa [prefixWord, tailWord_8007605, baseEnd_8007605] using wordTrace_append hprefix tailTrace_8007605
  have hstable : (prefixWord ++ tailWord_8007605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007605).length < 2 ^ (prefixWord ++ tailWord_8007605).sum := by decide
  have hdescent : baseEnd_8007605 < baseStart_8007605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007615 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 3]
def baseStart_8007615 : Nat := 118140960795 + 8007615 * 2 ^ 59
def prefixEnd_8007615 : Nat := 4983230072969 + 3 ^ 40 * 8007615 * 2
def baseEnd_8007615 : Nat := 4111755391152792903186155

theorem tailTrace_8007615 : CollatzResearch.WordTrace tailWord_8007615 prefixEnd_8007615 4111755391152792903186155 := by
  unfold tailWord_8007615
  simp only [CollatzResearch.WordTrace]
  refine ⟨292061712884785921607568299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194707808589857281071712199 292061712884785921607568299)
  ·
    refine ⟨438092569327178882411352449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292061712884785921607568299 438092569327178882411352449)
    ·
      refine ⟨328569426995384161808514337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438092569327178882411352449 328569426995384161808514337)
      ·
        refine ⟨246427070246538121356385753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328569426995384161808514337 246427070246538121356385753)
        ·
          refine ⟨184820302684903591017289315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246427070246538121356385753 184820302684903591017289315)
          ·
            refine ⟨277230454027355386525933973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184820302684903591017289315 277230454027355386525933973)
            ·
              refine ⟨12995177532532283743403155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277230454027355386525933973 12995177532532283743403155)
              ·
                refine ⟨19492766298798425615104733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12995177532532283743403155 19492766298798425615104733)
                ·
                  refine ⟨7309787362049409605664275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19492766298798425615104733 7309787362049409605664275)
                  ·
                    refine ⟨10964681043074114408496413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7309787362049409605664275 10964681043074114408496413)
                    ·
                      refine ⟨4111755391152792903186155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10964681043074114408496413 4111755391152792903186155)
                      ·
                        rfl

theorem cell23_8007615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_8007615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007615 prefixEnd_8007615 := by exact prefixLift 8007615
  have htrace : WordTrace (prefixWord ++ tailWord_8007615) baseStart_8007615 baseEnd_8007615 := by
    simpa [prefixWord, tailWord_8007615, baseEnd_8007615] using wordTrace_append hprefix tailTrace_8007615
  have hstable : (prefixWord ++ tailWord_8007615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007615).length < 2 ^ (prefixWord ++ tailWord_8007615).sum := by decide
  have hdescent : baseEnd_8007615 < baseStart_8007615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007621 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_8007621 : Nat := 118140960795 + 8007621 * 2 ^ 59
def prefixEnd_8007621 : Nat := 4983230072969 + 3 ^ 40 * 8007621 * 2
def baseEnd_8007621 : Nat := 4111758472036719879711127

theorem tailTrace_8007621 : CollatzResearch.WordTrace tailWord_8007621 prefixEnd_8007621 4111758472036719879711127 := by
  unfold tailWord_8007621
  simp only [CollatzResearch.WordTrace]
  refine ⟨292061931722764184632286717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194707954481842789754857811 292061931722764184632286717)
  ·
    refine ⟨109523224396036569237107519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292061931722764184632286717 109523224396036569237107519)
    ·
      refine ⟨164284836594054853855661279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109523224396036569237107519 164284836594054853855661279)
      ·
        refine ⟨246427254891082280783491919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164284836594054853855661279 246427254891082280783491919)
        ·
          refine ⟨369640882336623421175237879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246427254891082280783491919 369640882336623421175237879)
          ·
            refine ⟨554461323504935131762856819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369640882336623421175237879 554461323504935131762856819)
            ·
              refine ⟨831691985257402697644285229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554461323504935131762856819 831691985257402697644285229)
              ·
                refine ⟨311884494471526011616606961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 831691985257402697644285229 311884494471526011616606961)
                ·
                  refine ⟨233913370853644508712455221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311884494471526011616606961 233913370853644508712455221)
                  ·
                    refine ⟨21929378517529172691792677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233913370853644508712455221 21929378517529172691792677)
                    ·
                      refine ⟨4111758472036719879711127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21929378517529172691792677 4111758472036719879711127)
                      ·
                        rfl

theorem cell23_8007621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_8007621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007621 prefixEnd_8007621 := by exact prefixLift 8007621
  have htrace : WordTrace (prefixWord ++ tailWord_8007621) baseStart_8007621 baseEnd_8007621 := by
    simpa [prefixWord, tailWord_8007621, baseEnd_8007621] using wordTrace_append hprefix tailTrace_8007621
  have hstable : (prefixWord ++ tailWord_8007621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007621).length < 2 ^ (prefixWord ++ tailWord_8007621).sum := by decide
  have hdescent : baseEnd_8007621 < baseStart_8007621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007672 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 3, 2, 2]
def baseStart_8007672 : Nat := 118140960795 + 8007672 * 2 ^ 59
def prefixEnd_8007672 : Nat := 4983230072969 + 3 ^ 40 * 8007672 * 2
def baseEnd_8007672 : Nat := 4111784659550099180173393

theorem tailTrace_8007672 : CollatzResearch.WordTrace tailWord_8007672 prefixEnd_8007672 4111784659550099180173393 := by
  unfold tailWord_8007672
  simp only [CollatzResearch.WordTrace]
  refine ⟨146031895922789710171196635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194709194563719613561595513 146031895922789710171196635)
  ·
    refine ⟨219047843884184565256794953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146031895922789710171196635 219047843884184565256794953)
    ·
      refine ⟨164285882913138423942596215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219047843884184565256794953 164285882913138423942596215)
      ·
        refine ⟨246428824369707635913894323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164285882913138423942596215 246428824369707635913894323)
        ·
          refine ⟨369643236554561453870841485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246428824369707635913894323 369643236554561453870841485)
          ·
            refine ⟨138616213707960545201565557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369643236554561453870841485 138616213707960545201565557)
            ·
              refine ⟨12995270035121301112646771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138616213707960545201565557 12995270035121301112646771)
              ·
                refine ⟨19492905052681951668970157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12995270035121301112646771 19492905052681951668970157)
                ·
                  refine ⟨7309839394755731875863809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19492905052681951668970157 7309839394755731875863809)
                  ·
                    refine ⟨5482379546066798906897857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7309839394755731875863809 5482379546066798906897857)
                    ·
                      refine ⟨4111784659550099180173393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482379546066798906897857 4111784659550099180173393)
                      ·
                        rfl

theorem cell23_8007672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_8007672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007672 prefixEnd_8007672 := by exact prefixLift 8007672
  have htrace : WordTrace (prefixWord ++ tailWord_8007672) baseStart_8007672 baseEnd_8007672 := by
    simpa [prefixWord, tailWord_8007672, baseEnd_8007672] using wordTrace_append hprefix tailTrace_8007672
  have hstable : (prefixWord ++ tailWord_8007672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007672).length < 2 ^ (prefixWord ++ tailWord_8007672).sum := by decide
  have hdescent : baseEnd_8007672 < baseStart_8007672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007686 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_8007686 : Nat := 118140960795 + 8007686 * 2 ^ 59
def prefixEnd_8007686 : Nat := 4983230072969 + 3 ^ 40 * 8007686 * 2
def baseEnd_8007686 : Nat := 1370597282759754041799443

theorem tailTrace_8007686 : CollatzResearch.WordTrace tailWord_8007686 prefixEnd_8007686 1370597282759754041799443 := by
  unfold tailWord_8007686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127009452110271897918841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194709534978352467155601941 9127009452110271897918841)
  ·
    refine ⟨6845257089082703923439131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9127009452110271897918841 6845257089082703923439131)
    ·
      refine ⟨10267885633624055885158697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6845257089082703923439131 10267885633624055885158697)
      ·
        refine ⟨7700914225218041913869023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10267885633624055885158697 7700914225218041913869023)
        ·
          refine ⟨11551371337827062870803535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700914225218041913869023 11551371337827062870803535)
          ·
            refine ⟨17327057006740594306205303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551371337827062870803535 17327057006740594306205303)
            ·
              refine ⟨25990585510110891459307955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17327057006740594306205303 25990585510110891459307955)
              ·
                refine ⟨38985878265166337188961933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25990585510110891459307955 38985878265166337188961933)
                ·
                  refine ⟨14619704349437376445860725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38985878265166337188961933 14619704349437376445860725)
                  ·
                    refine ⟨1370597282759754041799443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14619704349437376445860725 1370597282759754041799443)
                    ·
                      rfl

theorem cell23_8007686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_8007686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007686 prefixEnd_8007686 := by exact prefixLift 8007686
  have htrace : WordTrace (prefixWord ++ tailWord_8007686) baseStart_8007686 baseEnd_8007686 := by
    simpa [prefixWord, tailWord_8007686, baseEnd_8007686] using wordTrace_append hprefix tailTrace_8007686
  have hstable : (prefixWord ++ tailWord_8007686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007686).length < 2 ^ (prefixWord ++ tailWord_8007686).sum := by decide
  have hdescent : baseEnd_8007686 < baseStart_8007686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007693 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_8007693 : Nat := 118140960795 + 8007693 * 2 ^ 59
def prefixEnd_8007693 : Nat := 4983230072969 + 3 ^ 40 * 8007693 * 2
def baseEnd_8007693 : Nat := 4111795442643843598010797

theorem tailTrace_8007693 : CollatzResearch.WordTrace tailWord_8007693 prefixEnd_8007693 4111795442643843598010797 := by
  unfold tailWord_8007693
  simp only [CollatzResearch.WordTrace]
  refine ⟨292064557778503340928907733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194709705185668893952605155 292064557778503340928907733)
  ·
    refine ⟨6845263072933672053021275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 292064557778503340928907733 6845263072933672053021275)
    ·
      refine ⟨10267894609400508079531913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6845263072933672053021275 10267894609400508079531913)
      ·
        refine ⟨7700920957050381059648935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10267894609400508079531913 7700920957050381059648935)
        ·
          refine ⟨11551381435575571589473403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700920957050381059648935 11551381435575571589473403)
          ·
            refine ⟨17327072153363357384210105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551381435575571589473403 17327072153363357384210105)
            ·
              refine ⟨12995304115022518038157579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17327072153363357384210105 12995304115022518038157579)
              ·
                refine ⟨19492956172533777057236369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12995304115022518038157579 19492956172533777057236369)
                ·
                  refine ⟨14619717129400332792927277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19492956172533777057236369 14619717129400332792927277)
                  ·
                    refine ⟨5482393923525124797347729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14619717129400332792927277 5482393923525124797347729)
                    ·
                      refine ⟨4111795442643843598010797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482393923525124797347729 4111795442643843598010797)
                      ·
                        rfl

theorem cell23_8007693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_8007693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007693 prefixEnd_8007693 := by exact prefixLift 8007693
  have htrace : WordTrace (prefixWord ++ tailWord_8007693) baseStart_8007693 baseEnd_8007693 := by
    simpa [prefixWord, tailWord_8007693, baseEnd_8007693] using wordTrace_append hprefix tailTrace_8007693
  have hstable : (prefixWord ++ tailWord_8007693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007693).length < 2 ^ (prefixWord ++ tailWord_8007693).sum := by decide
  have hdescent : baseEnd_8007693 < baseStart_8007693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007709 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_8007709 : Nat := 118140960795 + 8007709 * 2 ^ 59
def prefixEnd_8007709 : Nat := 4983230072969 + 3 ^ 40 * 8007709 * 2
def baseEnd_8007709 : Nat := 4111803658334315535410723

theorem tailTrace_8007709 : CollatzResearch.WordTrace tailWord_8007709 prefixEnd_8007709 4111803658334315535410723 := by
  unfold tailWord_8007709
  simp only [CollatzResearch.WordTrace]
  refine ⟨292065141346445375661490181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194710094230963583774326787 292065141346445375661490181)
  ·
    refine ⟨54762214002458507936529409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292065141346445375661490181 54762214002458507936529409)
    ·
      refine ⟨41071660501843880952397057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54762214002458507936529409 41071660501843880952397057)
      ·
        refine ⟨30803745376382910714297793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41071660501843880952397057 30803745376382910714297793)
        ·
          refine ⟨23102809032287183035723345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30803745376382910714297793 23102809032287183035723345)
          ·
            refine ⟨17327106774215387276792509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23102809032287183035723345 17327106774215387276792509)
            ·
              refine ⟨6497665040330770228797191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17327106774215387276792509 6497665040330770228797191)
              ·
                refine ⟨9746497560496155343195787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497665040330770228797191 9746497560496155343195787)
                ·
                  refine ⟨14619746340744233014793681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9746497560496155343195787 14619746340744233014793681)
                  ·
                    refine ⟨10964809755558174761095261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14619746340744233014793681 10964809755558174761095261)
                    ·
                      refine ⟨4111803658334315535410723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10964809755558174761095261 4111803658334315535410723)
                      ·
                        rfl

theorem cell23_8007709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_8007709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007709 prefixEnd_8007709 := by exact prefixLift 8007709
  have htrace : WordTrace (prefixWord ++ tailWord_8007709) baseStart_8007709 baseEnd_8007709 := by
    simpa [prefixWord, tailWord_8007709, baseEnd_8007709] using wordTrace_append hprefix tailTrace_8007709
  have hstable : (prefixWord ++ tailWord_8007709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007709).length < 2 ^ (prefixWord ++ tailWord_8007709).sum := by decide
  have hdescent : baseEnd_8007709 < baseStart_8007709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007728 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 4]
def baseStart_8007728 : Nat := 118140960795 + 8007728 * 2 ^ 59
def prefixEnd_8007728 : Nat := 4983230072969 + 3 ^ 40 * 8007728 * 2
def baseEnd_8007728 : Nat := 4111813414466750961073135

theorem tailTrace_8007728 : CollatzResearch.WordTrace tailWord_8007728 prefixEnd_8007728 4111813414466750961073135 := by
  unfold tailWord_8007728
  simp only [CollatzResearch.WordTrace]
  refine ⟨146032917166688270953215919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194710556222251027937621225 146032917166688270953215919)
  ·
    refine ⟨219049375750032406429823879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146032917166688270953215919 219049375750032406429823879)
    ·
      refine ⟨328574063625048609644735819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219049375750032406429823879 328574063625048609644735819)
      ·
        refine ⟨492861095437572914467103729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328574063625048609644735819 492861095437572914467103729)
        ·
          refine ⟨369645821578179685850327797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492861095437572914467103729 369645821578179685850327797)
          ·
            refine ⟨34654295772954345548468231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 369645821578179685850327797 34654295772954345548468231)
            ·
              refine ⟨51981443659431518322702347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34654295772954345548468231 51981443659431518322702347)
              ·
                refine ⟨77972165489147277484053521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51981443659431518322702347 77972165489147277484053521)
                ·
                  refine ⟨58479124116860458113040141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77972165489147277484053521 58479124116860458113040141)
                  ·
                    refine ⟨21929671543822671792390053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58479124116860458113040141 21929671543822671792390053)
                    ·
                      refine ⟨4111813414466750961073135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21929671543822671792390053 4111813414466750961073135)
                      ·
                        rfl

theorem cell23_8007728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_8007728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007728 prefixEnd_8007728 := by exact prefixLift 8007728
  have htrace : WordTrace (prefixWord ++ tailWord_8007728) baseStart_8007728 baseEnd_8007728 := by
    simpa [prefixWord, tailWord_8007728, baseEnd_8007728] using wordTrace_append hprefix tailTrace_8007728
  have hstable : (prefixWord ++ tailWord_8007728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007728).length < 2 ^ (prefixWord ++ tailWord_8007728).sum := by decide
  have hdescent : baseEnd_8007728 < baseStart_8007728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007779 : List Nat := [1, 1, 1, 5, 1, 1, 5, 2, 2, 2, 2]
def baseStart_8007779 : Nat := 118140960795 + 8007779 * 2 ^ 59
def prefixEnd_8007779 : Nat := 4983230072969 + 3 ^ 40 * 8007779 * 2
def baseEnd_8007779 : Nat := 4111839601980130261535401

theorem tailTrace_8007779 : CollatzResearch.WordTrace tailWord_8007779 prefixEnd_8007779 4111839601980130261535401 := by
  unfold tailWord_8007779
  simp only [CollatzResearch.WordTrace]
  refine ⟨292067694456191777616538391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194711796304127851744358927 292067694456191777616538391)
  ·
    refine ⟨438101541684287666424807587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292067694456191777616538391 438101541684287666424807587)
    ·
      refine ⟨657152312526431499637211381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438101541684287666424807587 657152312526431499637211381)
      ·
        refine ⟨61608029299352953090988567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 657152312526431499637211381 61608029299352953090988567)
        ·
          refine ⟨92412043949029429636482851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61608029299352953090988567 92412043949029429636482851)
          ·
            refine ⟨138618065923544144454724277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92412043949029429636482851 138618065923544144454724277)
            ·
              refine ⟨12995443680332263542630401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138618065923544144454724277 12995443680332263542630401)
              ·
                refine ⟨9746582760249197656972801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12995443680332263542630401 9746582760249197656972801)
                ·
                  refine ⟨7309937070186898242729601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9746582760249197656972801 7309937070186898242729601)
                  ·
                    refine ⟨5482452802640173682047201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7309937070186898242729601 5482452802640173682047201)
                    ·
                      refine ⟨4111839601980130261535401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482452802640173682047201 4111839601980130261535401)
                      ·
                        rfl

theorem cell23_8007779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_8007779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007779 prefixEnd_8007779 := by exact prefixLift 8007779
  have htrace : WordTrace (prefixWord ++ tailWord_8007779) baseStart_8007779 baseEnd_8007779 := by
    simpa [prefixWord, tailWord_8007779, baseEnd_8007779] using wordTrace_append hprefix tailTrace_8007779
  have hstable : (prefixWord ++ tailWord_8007779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007779).length < 2 ^ (prefixWord ++ tailWord_8007779).sum := by decide
  have hdescent : baseEnd_8007779 < baseStart_8007779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007785 : List Nat := [1, 2, 1, 1, 1, 5, 1, 6, 5]
def baseStart_8007785 : Nat := 118140960795 + 8007785 * 2 ^ 59
def prefixEnd_8007785 : Nat := 4983230072969 + 3 ^ 40 * 8007785 * 2
def baseEnd_8007785 : Nat := 456871409207117470895597

theorem tailTrace_8007785 : CollatzResearch.WordTrace tailWord_8007785 prefixEnd_8007785 456871409207117470895597 := by
  unfold tailWord_8007785
  simp only [CollatzResearch.WordTrace]
  refine ⟨292067913294170040641256809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194711942196113360427504539 292067913294170040641256809)
  ·
    refine ⟨219050934970627530480942607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292067913294170040641256809 219050934970627530480942607)
    ·
      refine ⟨328576402455941295721413911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219050934970627530480942607 328576402455941295721413911)
      ·
        refine ⟨492864603683911943582120867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328576402455941295721413911 492864603683911943582120867)
        ·
          refine ⟨739296905525867915373181301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492864603683911943582120867 739296905525867915373181301)
          ·
            refine ⟨69309084893050117066235747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 739296905525867915373181301 69309084893050117066235747)
            ·
              refine ⟨103963627339575175599353621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69309084893050117066235747 103963627339575175599353621)
              ·
                refine ⟨4873295031542586356219701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103963627339575175599353621 4873295031542586356219701)
                ·
                  refine ⟨456871409207117470895597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4873295031542586356219701 456871409207117470895597)
                  ·
                    rfl

theorem cell23_8007785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 5].length) (baseStart_8007785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007785 prefixEnd_8007785 := by exact prefixLift 8007785
  have htrace : WordTrace (prefixWord ++ tailWord_8007785) baseStart_8007785 baseEnd_8007785 := by
    simpa [prefixWord, tailWord_8007785, baseEnd_8007785] using wordTrace_append hprefix tailTrace_8007785
  have hstable : (prefixWord ++ tailWord_8007785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007785).length < 2 ^ (prefixWord ++ tailWord_8007785).sum := by decide
  have hdescent : baseEnd_8007785 < baseStart_8007785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007808 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 5]
def baseStart_8007808 : Nat := 118140960795 + 8007808 * 2 ^ 59
def prefixEnd_8007808 : Nat := 4983230072969 + 3 ^ 40 * 8007808 * 2
def baseEnd_8007808 : Nat := 4111854492919110648072767

theorem tailTrace_8007808 : CollatzResearch.WordTrace tailWord_8007808 prefixEnd_8007808 4111854492919110648072767 := by
  unfold tailWord_8007808
  simp only [CollatzResearch.WordTrace]
  refine ⟨146034376086543357784672039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194712501448724477046229385 146034376086543357784672039)
  ·
    refine ⟨219051564129815036677008059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146034376086543357784672039 219051564129815036677008059)
    ·
      refine ⟨328577346194722555015512089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219051564129815036677008059 328577346194722555015512089)
      ·
        refine ⟨246433009646041916261634067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328577346194722555015512089 246433009646041916261634067)
        ·
          refine ⟨369649514469062874392451101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246433009646041916261634067 369649514469062874392451101)
          ·
            refine ⟨138618567925898577897169163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369649514469062874392451101 138618567925898577897169163)
            ·
              refine ⟨207927851888847866845753745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138618567925898577897169163 207927851888847866845753745)
              ·
                refine ⟨155945888916635900134315309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207927851888847866845753745 155945888916635900134315309)
                ·
                  refine ⟨58479708343738462550368241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155945888916635900134315309 58479708343738462550368241)
                  ·
                    refine ⟨43859781257803846912776181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58479708343738462550368241 43859781257803846912776181)
                    ·
                      refine ⟨4111854492919110648072767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43859781257803846912776181 4111854492919110648072767)
                      ·
                        rfl

theorem cell23_8007808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_8007808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007808 prefixEnd_8007808 := by exact prefixLift 8007808
  have htrace : WordTrace (prefixWord ++ tailWord_8007808) baseStart_8007808 baseEnd_8007808 := by
    simpa [prefixWord, tailWord_8007808, baseEnd_8007808] using wordTrace_append hprefix tailTrace_8007808
  have hstable : (prefixWord ++ tailWord_8007808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007808).length < 2 ^ (prefixWord ++ tailWord_8007808).sum := by decide
  have hdescent : baseEnd_8007808 < baseStart_8007808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007832 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 2, 5]
def baseStart_8007832 : Nat := 118140960795 + 8007832 * 2 ^ 59
def prefixEnd_8007832 : Nat := 4983230072969 + 3 ^ 40 * 8007832 * 2
def baseEnd_8007832 : Nat := 1370622272151606184724219

theorem tailTrace_8007832 : CollatzResearch.WordTrace tailWord_8007832 prefixEnd_8007832 1370622272151606184724219 := by
  unfold tailWord_8007832
  simp only [CollatzResearch.WordTrace]
  refine ⟨146034813762499883834108875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194713085016666511778811833 146034813762499883834108875)
  ·
    refine ⟨219052220643749825751163313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146034813762499883834108875 219052220643749825751163313)
    ·
      refine ⟨164289165482812369313372485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219052220643749825751163313 164289165482812369313372485)
      ·
        refine ⟨30804218528027319246257341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164289165482812369313372485 30804218528027319246257341)
        ·
          refine ⟨11551581948010244717346503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30804218528027319246257341 11551581948010244717346503)
          ·
            refine ⟨17327372922015367076019755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551581948010244717346503 17327372922015367076019755)
            ·
              refine ⟨25991059383023050614029633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17327372922015367076019755 25991059383023050614029633)
              ·
                refine ⟨19493294537267287960522225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25991059383023050614029633 19493294537267287960522225)
                ·
                  refine ⟨14619970902950465970391669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19493294537267287960522225 14619970902950465970391669)
                  ·
                    refine ⟨1370622272151606184724219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14619970902950465970391669 1370622272151606184724219)
                    ·
                      rfl

theorem cell23_8007832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_8007832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007832 prefixEnd_8007832 := by exact prefixLift 8007832
  have htrace : WordTrace (prefixWord ++ tailWord_8007832) baseStart_8007832 baseEnd_8007832 := by
    simpa [prefixWord, tailWord_8007832, baseEnd_8007832] using wordTrace_append hprefix tailTrace_8007832
  have hstable : (prefixWord ++ tailWord_8007832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007832).length < 2 ^ (prefixWord ++ tailWord_8007832).sum := by decide
  have hdescent : baseEnd_8007832 < baseStart_8007832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007835 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 3, 6, 2]
def baseStart_8007835 : Nat := 118140960795 + 8007835 * 2 ^ 59
def prefixEnd_8007835 : Nat := 4983230072969 + 3 ^ 40 * 8007835 * 2
def baseEnd_8007835 : Nat := 4111868356896782042435143

theorem tailTrace_8007835 : CollatzResearch.WordTrace tailWord_8007835 prefixEnd_8007835 4111868356896782042435143 := by
  unfold tailWord_8007835
  simp only [CollatzResearch.WordTrace]
  refine ⟨292069736943988899180576959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194713157962659266120384639 292069736943988899180576959)
  ·
    refine ⟨438104605415983348770865439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292069736943988899180576959 438104605415983348770865439)
    ·
      refine ⟨657156908123975023156298159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438104605415983348770865439 657156908123975023156298159)
      ·
        refine ⟨985735362185962534734447239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657156908123975023156298159 985735362185962534734447239)
        ·
          refine ⟨1478603043278943802101670859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985735362185962534734447239 1478603043278943802101670859)
          ·
            refine ⟨2217904564918415703152506289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478603043278943802101670859 2217904564918415703152506289)
            ·
              refine ⟨1663428423688811777364379717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217904564918415703152506289 1663428423688811777364379717)
              ·
                refine ⟨311892829441652208255821197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1663428423688811777364379717 311892829441652208255821197)
                ·
                  refine ⟨116959811040619578095932949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311892829441652208255821197 116959811040619578095932949)
                  ·
                    refine ⟨5482491142529042723246857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116959811040619578095932949 5482491142529042723246857)
                    ·
                      refine ⟨4111868356896782042435143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482491142529042723246857 4111868356896782042435143)
                      ·
                        rfl

theorem cell23_8007835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 6, 2].length) (baseStart_8007835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007835 prefixEnd_8007835 := by exact prefixLift 8007835
  have htrace : WordTrace (prefixWord ++ tailWord_8007835) baseStart_8007835 baseEnd_8007835 := by
    simpa [prefixWord, tailWord_8007835, baseEnd_8007835] using wordTrace_append hprefix tailTrace_8007835
  have hstable : (prefixWord ++ tailWord_8007835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007835).length < 2 ^ (prefixWord ++ tailWord_8007835).sum := by decide
  have hdescent : baseEnd_8007835 < baseStart_8007835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007842 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_8007842 : Nat := 118140960795 + 8007842 * 2 ^ 59
def prefixEnd_8007842 : Nat := 4983230072969 + 3 ^ 40 * 8007842 * 2
def baseEnd_8007842 : Nat := 4111871951261363515047611

theorem tailTrace_8007842 : CollatzResearch.WordTrace tailWord_8007842 prefixEnd_8007842 4111871951261363515047611 := by
  unfold tailWord_8007842
  simp only [CollatzResearch.WordTrace]
  refine ⟨73017498063740884844020445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194713328169975692917387853 73017498063740884844020445)
  ·
    refine ⟨27381561773902831816507667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73017498063740884844020445 27381561773902831816507667)
    ·
      refine ⟨41072342660854247724761501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27381561773902831816507667 41072342660854247724761501)
      ·
        refine ⟨15402128497820342896785563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41072342660854247724761501 15402128497820342896785563)
        ·
          refine ⟨23103192746730514345178345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15402128497820342896785563 23103192746730514345178345)
          ·
            refine ⟨17327394560047885758883759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23103192746730514345178345 17327394560047885758883759)
            ·
              refine ⟨25991091840071828638325639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17327394560047885758883759 25991091840071828638325639)
              ·
                refine ⟨38986637760107742957488459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25991091840071828638325639 38986637760107742957488459)
                ·
                  refine ⟨58479956640161614436232689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38986637760107742957488459 58479956640161614436232689)
                  ·
                    refine ⟨43859967480121210827174517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58479956640161614436232689 43859967480121210827174517)
                    ·
                      refine ⟨4111871951261363515047611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43859967480121210827174517 4111871951261363515047611)
                      ·
                        rfl

theorem cell23_8007842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_8007842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007842 prefixEnd_8007842 := by exact prefixLift 8007842
  have htrace : WordTrace (prefixWord ++ tailWord_8007842) baseStart_8007842 baseEnd_8007842 := by
    simpa [prefixWord, tailWord_8007842, baseEnd_8007842] using wordTrace_append hprefix tailTrace_8007842
  have hstable : (prefixWord ++ tailWord_8007842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007842).length < 2 ^ (prefixWord ++ tailWord_8007842).sum := by decide
  have hdescent : baseEnd_8007842 < baseStart_8007842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007855 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 3]
def baseStart_8007855 : Nat := 118140960795 + 8007855 * 2 ^ 59
def prefixEnd_8007855 : Nat := 4983230072969 + 3 ^ 40 * 8007855 * 2
def baseEnd_8007855 : Nat := 4111878626509871964185051

theorem tailTrace_8007855 : CollatzResearch.WordTrace tailWord_8007855 prefixEnd_8007855 4111878626509871964185051 := by
  unfold tailWord_8007855
  simp only [CollatzResearch.WordTrace]
  refine ⟨292070466403916442596305019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194713644269277628397536679 292070466403916442596305019)
  ·
    refine ⟨438105699605874663894457529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292070466403916442596305019 438105699605874663894457529)
    ·
      refine ⟨328579274704405997920843147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438105699605874663894457529 328579274704405997920843147)
      ·
        refine ⟨492868912056608996881264721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328579274704405997920843147 492868912056608996881264721)
        ·
          refine ⟨369651684042456747660948541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492868912056608996881264721 369651684042456747660948541)
          ·
            refine ⟨138619381515921280372855703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369651684042456747660948541 138619381515921280372855703)
            ·
              refine ⟨207929072273881920559283555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138619381515921280372855703 207929072273881920559283555)
              ·
                refine ⟨311893608410822880838925333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207929072273881920559283555 311893608410822880838925333)
                ·
                  refine ⟨14620012894257322539324625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 311893608410822880838925333 14620012894257322539324625)
                  ·
                    refine ⟨10965009670692991904493469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14620012894257322539324625 10965009670692991904493469)
                    ·
                      refine ⟨4111878626509871964185051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965009670692991904493469 4111878626509871964185051)
                      ·
                        rfl

theorem cell23_8007855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_8007855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007855 prefixEnd_8007855 := by exact prefixLift 8007855
  have htrace : WordTrace (prefixWord ++ tailWord_8007855) baseStart_8007855 baseEnd_8007855 := by
    simpa [prefixWord, tailWord_8007855, baseEnd_8007855] using wordTrace_append hprefix tailTrace_8007855
  have hstable : (prefixWord ++ tailWord_8007855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007855).length < 2 ^ (prefixWord ++ tailWord_8007855).sum := by decide
  have hdescent : baseEnd_8007855 < baseStart_8007855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007872 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 3]
def baseStart_8007872 : Nat := 118140960795 + 8007872 * 2 ^ 59
def prefixEnd_8007872 : Nat := 4983230072969 + 3 ^ 40 * 8007872 * 2
def baseEnd_8007872 : Nat := 4111887355680998397672473

theorem tailTrace_8007872 : CollatzResearch.WordTrace tailWord_8007872 prefixEnd_8007872 4111887355680998397672473 := by
  unfold tailWord_8007872
  simp only [CollatzResearch.WordTrace]
  refine ⟨146035543222427427249836935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194714057629903236333115913 146035543222427427249836935)
  ·
    refine ⟨219053314833641140874755403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146035543222427427249836935 219053314833641140874755403)
    ·
      refine ⟨328579972250461711312133105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219053314833641140874755403 328579972250461711312133105)
      ·
        refine ⟨246434979187846283484099829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328579972250461711312133105 246434979187846283484099829)
        ·
          refine ⟨23103279298860589076634359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246434979187846283484099829 23103279298860589076634359)
          ·
            refine ⟨34654918948290883614951539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23103279298860589076634359 34654918948290883614951539)
            ·
              refine ⟨51982378422436325422427309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34654918948290883614951539 51982378422436325422427309)
              ·
                refine ⟨19493391908413622033410241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51982378422436325422427309 19493391908413622033410241)
                ·
                  refine ⟨14620043931310216525057681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19493391908413622033410241 14620043931310216525057681)
                  ·
                    refine ⟨10965032948482662393793261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14620043931310216525057681 10965032948482662393793261)
                    ·
                      refine ⟨4111887355680998397672473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965032948482662393793261 4111887355680998397672473)
                      ·
                        rfl

theorem cell23_8007872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_8007872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007872 prefixEnd_8007872 := by exact prefixLift 8007872
  have htrace : WordTrace (prefixWord ++ tailWord_8007872) baseStart_8007872 baseEnd_8007872 := by
    simpa [prefixWord, tailWord_8007872, baseEnd_8007872] using wordTrace_append hprefix tailTrace_8007872
  have hstable : (prefixWord ++ tailWord_8007872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007872).length < 2 ^ (prefixWord ++ tailWord_8007872).sum := by decide
  have hdescent : baseEnd_8007872 < baseStart_8007872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007896 : List Nat := [2, 1, 2, 2, 4, 1, 4, 2, 1, 4]
def baseStart_8007896 : Nat := 118140960795 + 8007896 * 2 ^ 59
def prefixEnd_8007896 : Nat := 4983230072969 + 3 ^ 40 * 8007896 * 2
def baseEnd_8007896 : Nat := 1370633226405568767924121

theorem tailTrace_8007896 : CollatzResearch.WordTrace tailWord_8007896 prefixEnd_8007896 1370633226405568767924121 := by
  unfold tailWord_8007896
  simp only [CollatzResearch.WordTrace]
  refine ⟨146035980898383953299273771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194714641197845271065698361 146035980898383953299273771)
  ·
    refine ⟨219053971347575929948910657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146035980898383953299273771 219053971347575929948910657)
    ·
      refine ⟨164290478510681947461682993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219053971347575929948910657 164290478510681947461682993)
      ·
        refine ⟨123217858883011460596262245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164290478510681947461682993 123217858883011460596262245)
        ·
          refine ⟨23103348540564648861799171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123217858883011460596262245 23103348540564648861799171)
          ·
            refine ⟨34655022810846973292698757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23103348540564648861799171 34655022810846973292698757)
            ·
              refine ⟨6497816777033807492381017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34655022810846973292698757 6497816777033807492381017)
              ·
                refine ⟨4873362582775355619285763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497816777033807492381017 4873362582775355619285763)
                ·
                  refine ⟨7310043874163033428928645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873362582775355619285763 7310043874163033428928645)
                  ·
                    refine ⟨1370633226405568767924121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7310043874163033428928645 1370633226405568767924121)
                    ·
                      rfl

theorem cell23_8007896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_8007896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007896 prefixEnd_8007896 := by exact prefixLift 8007896
  have htrace : WordTrace (prefixWord ++ tailWord_8007896) baseStart_8007896 baseEnd_8007896 := by
    simpa [prefixWord, tailWord_8007896, baseEnd_8007896] using wordTrace_append hprefix tailTrace_8007896
  have hstable : (prefixWord ++ tailWord_8007896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007896).length < 2 ^ (prefixWord ++ tailWord_8007896).sum := by decide
  have hdescent : baseEnd_8007896 < baseStart_8007896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007905 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 5, 5]
def baseStart_8007905 : Nat := 118140960795 + 8007905 * 2 ^ 59
def prefixEnd_8007905 : Nat := 4983230072969 + 3 ^ 40 * 8007905 * 2
def baseEnd_8007905 : Nat := 1370634766847532256186607

theorem tailTrace_8007905 : CollatzResearch.WordTrace tailWord_8007905 prefixEnd_8007905 1370634766847532256186607 := by
  unfold tailWord_8007905
  simp only [CollatzResearch.WordTrace]
  refine ⟨292072290053735301135625169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194714860035823534090416779 292072290053735301135625169)
  ·
    refine ⟨219054217540301475851718877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292072290053735301135625169 219054217540301475851718877)
    ·
      refine ⟨82145331577613053444394579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219054217540301475851718877 82145331577613053444394579)
      ·
        refine ⟨123217997366419580166591869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82145331577613053444394579 123217997366419580166591869)
        ·
          refine ⟨46206749012407342562471951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123217997366419580166591869 46206749012407342562471951)
          ·
            refine ⟨69310123518611013843707927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46206749012407342562471951 69310123518611013843707927)
            ·
              refine ⟨103965185277916520765561891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69310123518611013843707927 103965185277916520765561891)
              ·
                refine ⟨155947777916874781148342837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103965185277916520765561891 155947777916874781148342837)
                ·
                  refine ⟨14620104179707010732657141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155947777916874781148342837 14620104179707010732657141)
                  ·
                    refine ⟨1370634766847532256186607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14620104179707010732657141 1370634766847532256186607)
                    ·
                      rfl

theorem cell23_8007905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_8007905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007905 prefixEnd_8007905 := by exact prefixLift 8007905
  have htrace : WordTrace (prefixWord ++ tailWord_8007905) baseStart_8007905 baseEnd_8007905 := by
    simpa [prefixWord, tailWord_8007905, baseEnd_8007905] using wordTrace_append hprefix tailTrace_8007905
  have hstable : (prefixWord ++ tailWord_8007905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007905).length < 2 ^ (prefixWord ++ tailWord_8007905).sum := by decide
  have hdescent : baseEnd_8007905 < baseStart_8007905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007919 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 3]
def baseStart_8007919 : Nat := 118140960795 + 8007919 * 2 ^ 59
def prefixEnd_8007919 : Nat := 4983230072969 + 3 ^ 40 * 8007919 * 2
def baseEnd_8007919 : Nat := 4111911489271759713784757

theorem tailTrace_8007919 : CollatzResearch.WordTrace tailWord_8007919 prefixEnd_8007919 4111911489271759713784757 := by
  unfold tailWord_8007919
  simp only [CollatzResearch.WordTrace]
  refine ⟨292072800675684581526634811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194715200450456387684423207 292072800675684581526634811)
  ·
    refine ⟨438109201013526872289952217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292072800675684581526634811 438109201013526872289952217)
    ·
      refine ⟨328581900760145154217464163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438109201013526872289952217 328581900760145154217464163)
      ·
        refine ⟨492872851140217731326196245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328581900760145154217464163 492872851140217731326196245)
        ·
          refine ⟨23103414897197706155915449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 492872851140217731326196245 23103414897197706155915449)
          ·
            refine ⟨17327561172898279616936587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23103414897197706155915449 17327561172898279616936587)
            ·
              refine ⟨25991341759347419425404881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17327561172898279616936587 25991341759347419425404881)
              ·
                refine ⟨19493506319510564569053661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25991341759347419425404881 19493506319510564569053661)
                ·
                  refine ⟨7310064869816461713395123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19493506319510564569053661 7310064869816461713395123)
                  ·
                    refine ⟨10965097304724692570092685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7310064869816461713395123 10965097304724692570092685)
                    ·
                      refine ⟨4111911489271759713784757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965097304724692570092685 4111911489271759713784757)
                      ·
                        rfl

theorem cell23_8007919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 3].length) (baseStart_8007919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007919 prefixEnd_8007919 := by exact prefixLift 8007919
  have htrace : WordTrace (prefixWord ++ tailWord_8007919) baseStart_8007919 baseEnd_8007919 := by
    simpa [prefixWord, tailWord_8007919, baseEnd_8007919] using wordTrace_append hprefix tailTrace_8007919
  have hstable : (prefixWord ++ tailWord_8007919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007919).length < 2 ^ (prefixWord ++ tailWord_8007919).sum := by decide
  have hdescent : baseEnd_8007919 < baseStart_8007919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007922 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_8007922 : Nat := 118140960795 + 8007922 * 2 ^ 59
def prefixEnd_8007922 : Nat := 4983230072969 + 3 ^ 40 * 8007922 * 2
def baseEnd_8007922 : Nat := 1370637676571241067349081

theorem tailTrace_8007922 : CollatzResearch.WordTrace tailWord_8007922 prefixEnd_8007922 1370637676571241067349081 := by
  unfold tailWord_8007922
  simp only [CollatzResearch.WordTrace]
  refine ⟨73018227523668428259748505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194715273396449142025996013 73018227523668428259748505)
  ·
    refine ⟨54763670642751321194811379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73018227523668428259748505 54763670642751321194811379)
    ·
      refine ⟨82145505964126981792217069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54763670642751321194811379 82145505964126981792217069)
      ·
        refine ⟨30804564736547618172081401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82145505964126981792217069 30804564736547618172081401)
        ·
          refine ⟨23103423552410713629061051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30804564736547618172081401 23103423552410713629061051)
          ·
            refine ⟨34655135328616070443591577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23103423552410713629061051 34655135328616070443591577)
            ·
              refine ⟨25991351496462052832693683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34655135328616070443591577 25991351496462052832693683)
              ·
                refine ⟨38987027244693079249040525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25991351496462052832693683 38987027244693079249040525)
                ·
                  refine ⟨14620135216759904718390197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38987027244693079249040525 14620135216759904718390197)
                  ·
                    refine ⟨1370637676571241067349081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14620135216759904718390197 1370637676571241067349081)
                    ·
                      rfl

theorem cell23_8007922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_8007922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007922 prefixEnd_8007922 := by exact prefixLift 8007922
  have htrace : WordTrace (prefixWord ++ tailWord_8007922) baseStart_8007922 baseEnd_8007922 := by
    simpa [prefixWord, tailWord_8007922, baseEnd_8007922] using wordTrace_append hprefix tailTrace_8007922
  have hstable : (prefixWord ++ tailWord_8007922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007922).length < 2 ^ (prefixWord ++ tailWord_8007922).sum := by decide
  have hdescent : baseEnd_8007922 < baseStart_8007922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007935 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 1, 6]
def baseStart_8007935 : Nat := 118140960795 + 8007935 * 2 ^ 59
def prefixEnd_8007935 : Nat := 4983230072969 + 3 ^ 40 * 8007935 * 2
def baseEnd_8007935 : Nat := 1370639901654077217061561

theorem tailTrace_8007935 : CollatzResearch.WordTrace tailWord_8007935 prefixEnd_8007935 1370639901654077217061561 := by
  unfold tailWord_8007935
  simp only [CollatzResearch.WordTrace]
  refine ⟨292073384243626616259217259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194715589495751077506144839 292073384243626616259217259)
  ·
    refine ⟨438110076365439924388825889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292073384243626616259217259 438110076365439924388825889)
    ·
      refine ⟨328582557274079943291619417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438110076365439924388825889 328582557274079943291619417)
      ·
        refine ⟨246436917955559957468714563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328582557274079943291619417 246436917955559957468714563)
        ·
          refine ⟨369655376933339936203071845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246436917955559957468714563 369655376933339936203071845)
          ·
            refine ⟨69310383175001238038075971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369655376933339936203071845 69310383175001238038075971)
            ·
              refine ⟨103965574762501857057113957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69310383175001238038075971 103965574762501857057113957)
              ·
                refine ⟨19493545267969098198208867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103965574762501857057113957 19493545267969098198208867)
                ·
                  refine ⟨29240317901953647297313301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19493545267969098198208867 29240317901953647297313301)
                  ·
                    refine ⟨1370639901654077217061561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29240317901953647297313301 1370639901654077217061561)
                    ·
                      rfl

theorem cell23_8007935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_8007935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007935 prefixEnd_8007935 := by exact prefixLift 8007935
  have htrace : WordTrace (prefixWord ++ tailWord_8007935) baseStart_8007935 baseEnd_8007935 := by
    simpa [prefixWord, tailWord_8007935, baseEnd_8007935] using wordTrace_append hprefix tailTrace_8007935
  have hstable : (prefixWord ++ tailWord_8007935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007935).length < 2 ^ (prefixWord ++ tailWord_8007935).sum := by decide
  have hdescent : baseEnd_8007935 < baseStart_8007935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007955 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 4]
def baseStart_8007955 : Nat := 118140960795 + 8007955 * 2 ^ 59
def prefixEnd_8007955 : Nat := 4983230072969 + 3 ^ 40 * 8007955 * 2
def baseEnd_8007955 : Nat := 4111929974575321572934591

theorem tailTrace_8007955 : CollatzResearch.WordTrace tailWord_8007955 prefixEnd_8007955 4111929974575321572934591 := by
  unfold tailWord_8007955
  simp only [CollatzResearch.WordTrace]
  refine ⟨292074113703554159674945319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194716075802369439783296879 292074113703554159674945319)
  ·
    refine ⟨438111170555331239512417979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292074113703554159674945319 438111170555331239512417979)
    ·
      refine ⟨657166755832996859268626969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438111170555331239512417979 657166755832996859268626969)
      ·
        refine ⟨492875066874747644451470227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657166755832996859268626969 492875066874747644451470227)
        ·
          refine ⟨739312600312121466677205341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492875066874747644451470227 739312600312121466677205341)
          ·
            refine ⟨277242225117045550003952003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 739312600312121466677205341 277242225117045550003952003)
            ·
              refine ⟨415863337675568325005928005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277242225117045550003952003 415863337675568325005928005)
              ·
                refine ⟨77974375814169060938611501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415863337675568325005928005 77974375814169060938611501)
                ·
                  refine ⟨29240390930313397851979313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77974375814169060938611501 29240390930313397851979313)
                  ·
                    refine ⟨21930293197735048388984485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29240390930313397851979313 21930293197735048388984485)
                    ·
                      refine ⟨4111929974575321572934591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21930293197735048388984485 4111929974575321572934591)
                      ·
                        rfl

theorem cell23_8007955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_8007955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007955 prefixEnd_8007955 := by exact prefixLift 8007955
  have htrace : WordTrace (prefixWord ++ tailWord_8007955) baseStart_8007955 baseEnd_8007955 := by
    simpa [prefixWord, tailWord_8007955, baseEnd_8007955] using wordTrace_append hprefix tailTrace_8007955
  have hstable : (prefixWord ++ tailWord_8007955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007955).length < 2 ^ (prefixWord ++ tailWord_8007955).sum := by decide
  have hdescent : baseEnd_8007955 < baseStart_8007955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007972 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_8007972 : Nat := 118140960795 + 8007972 * 2 ^ 59
def prefixEnd_8007972 : Nat := 4983230072969 + 3 ^ 40 * 8007972 * 2
def baseEnd_8007972 : Nat := 4111938703746448006422013

theorem tailTrace_8007972 : CollatzResearch.WordTrace tailWord_8007972 prefixEnd_8007972 4111938703746448006422013 := by
  unfold tailWord_8007972
  simp only [CollatzResearch.WordTrace]
  refine ⟨146037366872246285789157085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194716489162995047718876113 146037366872246285789157085)
  ·
    refine ⟨54764012577092357170933907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146037366872246285789157085 54764012577092357170933907)
    ·
      refine ⟨82146018865638535756400861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54764012577092357170933907 82146018865638535756400861)
      ·
        refine ⟨30804757074614450908650323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82146018865638535756400861 30804757074614450908650323)
        ·
          refine ⟨46207135611921676362975485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30804757074614450908650323 46207135611921676362975485)
          ·
            refine ⟨17327675854470628636115807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46207135611921676362975485 17327675854470628636115807)
            ·
              refine ⟨25991513781705942954173711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17327675854470628636115807 25991513781705942954173711)
              ·
                refine ⟨38987270672558914431260567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25991513781705942954173711 38987270672558914431260567)
                ·
                  refine ⟨58480906008838371646890851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38987270672558914431260567 58480906008838371646890851)
                  ·
                    refine ⟨87721359013257557470336277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58480906008838371646890851 87721359013257557470336277)
                    ·
                      refine ⟨4111938703746448006422013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87721359013257557470336277 4111938703746448006422013)
                      ·
                        rfl

theorem cell23_8007972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_8007972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007972 prefixEnd_8007972 := by exact prefixLift 8007972
  have htrace : WordTrace (prefixWord ++ tailWord_8007972) baseStart_8007972 baseEnd_8007972 := by
    simpa [prefixWord, tailWord_8007972, baseEnd_8007972] using wordTrace_append hprefix tailTrace_8007972
  have hstable : (prefixWord ++ tailWord_8007972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007972).length < 2 ^ (prefixWord ++ tailWord_8007972).sum := by decide
  have hdescent : baseEnd_8007972 < baseStart_8007972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007976 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_8007976 : Nat := 118140960795 + 8007976 * 2 ^ 59
def prefixEnd_8007976 : Nat := 4983230072969 + 3 ^ 40 * 8007976 * 2
def baseEnd_8007976 : Nat := 4111940757669065990771995

theorem tailTrace_8007976 : CollatzResearch.WordTrace tailWord_8007976 prefixEnd_8007976 4111940757669065990771995 := by
  unfold tailWord_8007976
  simp only [CollatzResearch.WordTrace]
  refine ⟨146037439818239040130729891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194716586424318720174306521 146037439818239040130729891)
  ·
    refine ⟨219056159727358560196094837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146037439818239040130729891 219056159727358560196094837)
    ·
      refine ⟨20536514974439865018383891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219056159727358560196094837 20536514974439865018383891)
      ·
        refine ⟨30804772461659797527575837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20536514974439865018383891 30804772461659797527575837)
        ·
          refine ⟨11551789673122424072840939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30804772461659797527575837 11551789673122424072840939)
          ·
            refine ⟨17327684509683636109261409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11551789673122424072840939 17327684509683636109261409)
            ·
              refine ⟨12995763382262727081946057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17327684509683636109261409 12995763382262727081946057)
              ·
                refine ⟨9746822536697045311459543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12995763382262727081946057 9746822536697045311459543)
                ·
                  refine ⟨14620233805045567967189315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9746822536697045311459543 14620233805045567967189315)
                  ·
                    refine ⟨21930350707568351950783973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14620233805045567967189315 21930350707568351950783973)
                    ·
                      refine ⟨4111940757669065990771995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21930350707568351950783973 4111940757669065990771995)
                      ·
                        rfl

theorem cell23_8007976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_8007976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007976 prefixEnd_8007976 := by exact prefixLift 8007976
  have htrace : WordTrace (prefixWord ++ tailWord_8007976) baseStart_8007976 baseEnd_8007976 := by
    simpa [prefixWord, tailWord_8007976, baseEnd_8007976] using wordTrace_append hprefix tailTrace_8007976
  have hstable : (prefixWord ++ tailWord_8007976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007976).length < 2 ^ (prefixWord ++ tailWord_8007976).sum := by decide
  have hdescent : baseEnd_8007976 < baseStart_8007976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8007992 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_8007992 : Nat := 118140960795 + 8007992 * 2 ^ 59
def prefixEnd_8007992 : Nat := 4983230072969 + 3 ^ 40 * 8007992 * 2
def baseEnd_8007992 : Nat := 4111948973359537928171921

theorem tailTrace_8007992 : CollatzResearch.WordTrace tailWord_8007992 prefixEnd_8007992 4111948973359537928171921 := by
  unfold tailWord_8007992
  simp only [CollatzResearch.WordTrace]
  refine ⟨146037731602210057497021115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194716975469613409996028153 146037731602210057497021115)
  ·
    refine ⟨219056597403315086245531673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146037731602210057497021115 219056597403315086245531673)
    ·
      refine ⟨164292448052486314684148755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219056597403315086245531673 164292448052486314684148755)
      ·
        refine ⟨246438672078729472026223133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164292448052486314684148755 246438672078729472026223133)
        ·
          refine ⟨92414502029523552009833675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246438672078729472026223133 92414502029523552009833675)
          ·
            refine ⟨138621753044285328014750513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92414502029523552009833675 138621753044285328014750513)
            ·
              refine ⟨103966314783213996011062885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138621753044285328014750513 103966314783213996011062885)
              ·
                refine ⟨19493684021852624252074291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103966314783213996011062885 19493684021852624252074291)
                ·
                  refine ⟨29240526032778936378111437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19493684021852624252074291 29240526032778936378111437)
                  ·
                    refine ⟨10965197262292101141791789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29240526032778936378111437 10965197262292101141791789)
                    ·
                      refine ⟨4111948973359537928171921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965197262292101141791789 4111948973359537928171921)
                      ·
                        rfl

theorem cell23_8007992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_8007992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8007992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8007992 prefixEnd_8007992 := by exact prefixLift 8007992
  have htrace : WordTrace (prefixWord ++ tailWord_8007992) baseStart_8007992 baseEnd_8007992 := by
    simpa [prefixWord, tailWord_8007992, baseEnd_8007992] using wordTrace_append hprefix tailTrace_8007992
  have hstable : (prefixWord ++ tailWord_8007992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8007992).length < 2 ^ (prefixWord ++ tailWord_8007992).sum := by decide
  have hdescent : baseEnd_8007992 < baseStart_8007992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8007992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008009 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 3]
def baseStart_8008009 : Nat := 118140960795 + 8008009 * 2 ^ 59
def prefixEnd_8008009 : Nat := 4983230072969 + 3 ^ 40 * 8008009 * 2
def baseEnd_8008009 : Nat := 4111957702530664361659343

theorem tailTrace_8008009 : CollatzResearch.WordTrace tailWord_8008009 prefixEnd_8008009 4111957702530664361659343 := by
  unfold tailWord_8008009
  simp only [CollatzResearch.WordTrace]
  refine ⟨292076083245358526897411081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194717388830239017931607387 292076083245358526897411081)
  ·
    refine ⟨219057062434018895173058311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292076083245358526897411081 219057062434018895173058311)
    ·
      refine ⟨328585593651028342759587467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219057062434018895173058311 328585593651028342759587467)
      ·
        refine ⟨492878390476542514139381201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328585593651028342759587467 492878390476542514139381201)
        ·
          refine ⟨369658792857406885604535901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492878390476542514139381201 369658792857406885604535901)
          ·
            refine ⟨138622047321527582101700963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369658792857406885604535901 138622047321527582101700963)
            ·
              refine ⟨207933070982291373152551445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138622047321527582101700963 207933070982291373152551445)
              ·
                refine ⟨9746862702294908116525849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207933070982291373152551445 9746862702294908116525849)
                ·
                  refine ⟨7310147026721181087394387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9746862702294908116525849 7310147026721181087394387)
                  ·
                    refine ⟨10965220540081771631091581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7310147026721181087394387 10965220540081771631091581)
                    ·
                      refine ⟨4111957702530664361659343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965220540081771631091581 4111957702530664361659343)
                      ·
                        rfl

theorem cell23_8008009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 3].length) (baseStart_8008009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008009 prefixEnd_8008009 := by exact prefixLift 8008009
  have htrace : WordTrace (prefixWord ++ tailWord_8008009) baseStart_8008009 baseEnd_8008009 := by
    simpa [prefixWord, tailWord_8008009, baseEnd_8008009] using wordTrace_append hprefix tailTrace_8008009
  have hstable : (prefixWord ++ tailWord_8008009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008009).length < 2 ^ (prefixWord ++ tailWord_8008009).sum := by decide
  have hdescent : baseEnd_8008009 < baseStart_8008009 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008025 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 1, 8]
def baseStart_8008025 : Nat := 118140960795 + 8008025 * 2 ^ 59
def prefixEnd_8008025 : Nat := 4983230072969 + 3 ^ 40 * 8008025 * 2
def baseEnd_8008025 : Nat := 1370655306073712099686423

theorem tailTrace_8008025 : CollatzResearch.WordTrace tailWord_8008025 prefixEnd_8008025 1370655306073712099686423 := by
  unfold tailWord_8008025
  simp only [CollatzResearch.WordTrace]
  refine ⟨292076666813300561629993529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194717777875533707753329019 292076666813300561629993529)
  ·
    refine ⟨219057500109975421222495147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292076666813300561629993529 219057500109975421222495147)
    ·
      refine ⟨328586250164963131833742721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219057500109975421222495147 328586250164963131833742721)
      ·
        refine ⟨246439687623722348875307041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328586250164963131833742721 246439687623722348875307041)
        ·
          refine ⟨184829765717791761656480281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246439687623722348875307041 184829765717791761656480281)
          ·
            refine ⟨138622324288343821242360211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184829765717791761656480281 138622324288343821242360211)
            ·
              refine ⟨207933486432515731863540317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138622324288343821242360211 207933486432515731863540317)
              ·
                refine ⟨77975057412193399448827619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207933486432515731863540317 77975057412193399448827619)
                ·
                  refine ⟨116962586118290099173241429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77975057412193399448827619 116962586118290099173241429)
                  ·
                    refine ⟨1370655306073712099686423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116962586118290099173241429 1370655306073712099686423)
                    ·
                      rfl

theorem cell23_8008025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_8008025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008025 prefixEnd_8008025 := by exact prefixLift 8008025
  have htrace : WordTrace (prefixWord ++ tailWord_8008025) baseStart_8008025 baseEnd_8008025 := by
    simpa [prefixWord, tailWord_8008025, baseEnd_8008025] using wordTrace_append hprefix tailTrace_8008025
  have hstable : (prefixWord ++ tailWord_8008025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008025).length < 2 ^ (prefixWord ++ tailWord_8008025).sum := by decide
  have hdescent : baseEnd_8008025 < baseStart_8008025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008055 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 11]
def baseStart_8008055 : Nat := 118140960795 + 8008055 * 2 ^ 59
def prefixEnd_8008055 : Nat := 4983230072969 + 3 ^ 40 * 8008055 * 2
def baseEnd_8008055 : Nat := 456886813626752353520459

theorem tailTrace_8008055 : CollatzResearch.WordTrace tailWord_8008055 prefixEnd_8008055 456886813626752353520459 := by
  unfold tailWord_8008055
  simp only [CollatzResearch.WordTrace]
  refine ⟨292077761003191876753585619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194718507335461251169057079 292077761003191876753585619)
  ·
    refine ⟨438116641504787815130378429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292077761003191876753585619 438116641504787815130378429)
    ·
      refine ⟨164293740564295430673891911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438116641504787815130378429 164293740564295430673891911)
      ·
        refine ⟨246440610846443146010837867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164293740564295430673891911 246440610846443146010837867)
        ·
          refine ⟨369660916269664719016256801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246440610846443146010837867 369660916269664719016256801)
          ·
            refine ⟨277245687202248539262192601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369660916269664719016256801 277245687202248539262192601)
            ·
              refine ⟨207934265401686404446644451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277245687202248539262192601 207934265401686404446644451)
              ·
                refine ⟨311901398102529606669966677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207934265401686404446644451 311901398102529606669966677)
                ·
                  refine ⟨456886813626752353520459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 311901398102529606669966677 456886813626752353520459)
                  ·
                    rfl

theorem cell23_8008055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 11].length) (baseStart_8008055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008055 prefixEnd_8008055 := by exact prefixLift 8008055
  have htrace : WordTrace (prefixWord ++ tailWord_8008055) baseStart_8008055 baseEnd_8008055 := by
    simpa [prefixWord, tailWord_8008055, baseEnd_8008055] using wordTrace_append hprefix tailTrace_8008055
  have hstable : (prefixWord ++ tailWord_8008055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008055).length < 2 ^ (prefixWord ++ tailWord_8008055).sum := by decide
  have hdescent : baseEnd_8008055 < baseStart_8008055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008072 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 7]
def baseStart_8008072 : Nat := 118140960795 + 8008072 * 2 ^ 59
def prefixEnd_8008072 : Nat := 4983230072969 + 3 ^ 40 * 8008072 * 2
def baseEnd_8008072 : Nat := 456887783534655290574617

theorem tailTrace_8008072 : CollatzResearch.WordTrace tailWord_8008072 prefixEnd_8008072 456887783534655290574617 := by
  unfold tailWord_8008072
  simp only [CollatzResearch.WordTrace]
  refine ⟨146039190522065144328477235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194718920696086859104636313 146039190522065144328477235)
  ·
    refine ⟨219058785783097716492715853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146039190522065144328477235 219058785783097716492715853)
    ·
      refine ⟨82147044668661643684768445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219058785783097716492715853 82147044668661643684768445)
      ·
        refine ⟨30805141750748116381788167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82147044668661643684768445 30805141750748116381788167)
        ·
          refine ⟨46207712626122174572682251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30805141750748116381788167 46207712626122174572682251)
          ·
            refine ⟨69311568939183261859023377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46207712626122174572682251 69311568939183261859023377)
            ·
              refine ⟨51983676704387446394267533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69311568939183261859023377 51983676704387446394267533)
              ·
                refine ⟨19493878764145292397850325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51983676704387446394267533 19493878764145292397850325)
                ·
                  refine ⟨456887783534655290574617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19493878764145292397850325 456887783534655290574617)
                  ·
                    rfl

theorem cell23_8008072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 7].length) (baseStart_8008072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008072 prefixEnd_8008072 := by exact prefixLift 8008072
  have htrace : WordTrace (prefixWord ++ tailWord_8008072) baseStart_8008072 baseEnd_8008072 := by
    simpa [prefixWord, tailWord_8008072, baseEnd_8008072] using wordTrace_append hprefix tailTrace_8008072
  have hstable : (prefixWord ++ tailWord_8008072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008072).length < 2 ^ (prefixWord ++ tailWord_8008072).sum := by decide
  have hdescent : baseEnd_8008072 < baseStart_8008072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008117 : List Nat := [1, 3, 3, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_8008117 : Nat := 118140960795 + 8008117 * 2 ^ 59
def prefixEnd_8008117 : Nat := 4983230072969 + 3 ^ 40 * 8008117 * 2
def baseEnd_8008117 : Nat := 4112013158441349939108847

theorem tailTrace_8008117 : CollatzResearch.WordTrace tailWord_8008117 prefixEnd_8008117 4112013158441349939108847 := by
  unfold tailWord_8008117
  simp only [CollatzResearch.WordTrace]
  refine ⟨292080022328967261342342605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194720014885978174228228403 292080022328967261342342605)
  ·
    refine ⟨109530008373362723003378477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292080022328967261342342605 109530008373362723003378477)
    ·
      refine ⟨41073753140011021126266929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109530008373362723003378477 41073753140011021126266929)
      ·
        refine ⟨30805314855008265844700197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41073753140011021126266929 30805314855008265844700197)
        ·
          refine ⟨5775996535314049845881287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30805314855008265844700197 5775996535314049845881287)
          ·
            refine ⟨8663994802971074768821931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775996535314049845881287 8663994802971074768821931)
            ·
              refine ⟨12995992204456612153232897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663994802971074768821931 12995992204456612153232897)
              ·
                refine ⟨9746994153342459114924673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12995992204456612153232897 9746994153342459114924673)
                ·
                  refine ⟨7310245615006844336193505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9746994153342459114924673 7310245615006844336193505)
                  ·
                    refine ⟨5482684211255133252145129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7310245615006844336193505 5482684211255133252145129)
                    ·
                      refine ⟨4112013158441349939108847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482684211255133252145129 4112013158441349939108847)
                      ·
                        rfl

theorem cell23_8008117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_8008117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008117 prefixEnd_8008117 := by exact prefixLift 8008117
  have htrace : WordTrace (prefixWord ++ tailWord_8008117) baseStart_8008117 baseEnd_8008117 := by
    simpa [prefixWord, tailWord_8008117, baseEnd_8008117] using wordTrace_append hprefix tailTrace_8008117
  have hstable : (prefixWord ++ tailWord_8008117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008117).length < 2 ^ (prefixWord ++ tailWord_8008117).sum := by decide
  have hdescent : baseEnd_8008117 < baseStart_8008117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008152 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_8008152 : Nat := 118140960795 + 8008152 * 2 ^ 59
def prefixEnd_8008152 : Nat := 4983230072969 + 3 ^ 40 * 8008152 * 2
def baseEnd_8008152 : Nat := 4112031130264257302171185

theorem tailTrace_8008152 : CollatzResearch.WordTrace tailWord_8008152 prefixEnd_8008152 4112031130264257302171185 := by
  unfold tailWord_8008152
  simp only [CollatzResearch.WordTrace]
  refine ⟨146040649441920231159933355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194720865922560308213244473 146040649441920231159933355)
  ·
    refine ⟨219060974162880346739900033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146040649441920231159933355 219060974162880346739900033)
    ·
      refine ⟨164295730622160260054925025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219060974162880346739900033 164295730622160260054925025)
      ·
        refine ⟨123221797966620195041193769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164295730622160260054925025 123221797966620195041193769)
        ·
          refine ⟨92416348474965146280895327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123221797966620195041193769 92416348474965146280895327)
          ·
            refine ⟨138624522712447719421342991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92416348474965146280895327 138624522712447719421342991)
            ·
              refine ⟨207936784068671579132014487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138624522712447719421342991 207936784068671579132014487)
              ·
                refine ⟨311905176103007368698021731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207936784068671579132014487 311905176103007368698021731)
                ·
                  refine ⟨467857764154511053047032597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311905176103007368698021731 467857764154511053047032597)
                  ·
                    refine ⟨21930832694742705611579653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 467857764154511053047032597 21930832694742705611579653)
                    ·
                      refine ⟨4112031130264257302171185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21930832694742705611579653 4112031130264257302171185)
                      ·
                        rfl

theorem cell23_8008152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_8008152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008152 prefixEnd_8008152 := by exact prefixLift 8008152
  have htrace : WordTrace (prefixWord ++ tailWord_8008152) baseStart_8008152 baseEnd_8008152 := by
    simpa [prefixWord, tailWord_8008152, baseEnd_8008152] using wordTrace_append hprefix tailTrace_8008152
  have hstable : (prefixWord ++ tailWord_8008152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008152).length < 2 ^ (prefixWord ++ tailWord_8008152).sum := by decide
  have hdescent : baseEnd_8008152 < baseStart_8008152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008159 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 3]
def baseStart_8008159 : Nat := 118140960795 + 8008159 * 2 ^ 59
def prefixEnd_8008159 : Nat := 4983230072969 + 3 ^ 40 * 8008159 * 2
def baseEnd_8008159 : Nat := 4112034724628838774783653

theorem tailTrace_8008159 : CollatzResearch.WordTrace tailWord_8008159 prefixEnd_8008159 4112034724628838774783653 := by
  unfold tailWord_8008159
  simp only [CollatzResearch.WordTrace]
  refine ⟨292081554194815102515371531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194721036129876735010247687 292081554194815102515371531)
  ·
    refine ⟨438122331292222653773057297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292081554194815102515371531 438122331292222653773057297)
    ·
      refine ⟨328591748469166990329792973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438122331292222653773057297 328591748469166990329792973)
      ·
        refine ⟨123221905675937621373672365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328591748469166990329792973 123221905675937621373672365)
        ·
          refine ⟨46208214628476608015127137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123221905675937621373672365 46208214628476608015127137)
          ·
            refine ⟨34656160971357456011345353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46208214628476608015127137 34656160971357456011345353)
            ·
              refine ⟨25992120728518092008509015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34656160971357456011345353 25992120728518092008509015)
              ·
                refine ⟨38988181092777138012763523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25992120728518092008509015 38988181092777138012763523)
                ·
                  refine ⟨58482271639165707019145285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38988181092777138012763523 58482271639165707019145285)
                  ·
                    refine ⟨10965425932343570066089741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58482271639165707019145285 10965425932343570066089741)
                    ·
                      refine ⟨4112034724628838774783653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965425932343570066089741 4112034724628838774783653)
                      ·
                        rfl

theorem cell23_8008159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_8008159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008159 prefixEnd_8008159 := by exact prefixLift 8008159
  have htrace : WordTrace (prefixWord ++ tailWord_8008159) baseStart_8008159 baseEnd_8008159 := by
    simpa [prefixWord, tailWord_8008159, baseEnd_8008159] using wordTrace_append hprefix tailTrace_8008159
  have hstable : (prefixWord ++ tailWord_8008159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008159).length < 2 ^ (prefixWord ++ tailWord_8008159).sum := by decide
  have hdescent : baseEnd_8008159 < baseStart_8008159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008196 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 6]
def baseStart_8008196 : Nat := 118140960795 + 8008196 * 2 ^ 59
def prefixEnd_8008196 : Nat := 4983230072969 + 3 ^ 40 * 8008196 * 2
def baseEnd_8008196 : Nat := 456894858157006125557887

theorem tailTrace_8008196 : CollatzResearch.WordTrace tailWord_8008196 prefixEnd_8008196 456894858157006125557887 := by
  unfold tailWord_8008196
  simp only [CollatzResearch.WordTrace]
  refine ⟨146041451847840528917234221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194721935797120705222978961 146041451847840528917234221)
  ·
    refine ⟨54765544442940198343962833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146041451847840528917234221 54765544442940198343962833)
    ·
      refine ⟨41074158332205148757972125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54765544442940198343962833 41074158332205148757972125)
      ·
        refine ⟨15402809374576930784239547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41074158332205148757972125 15402809374576930784239547)
        ·
          refine ⟨23104214061865396176359321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15402809374576930784239547 23104214061865396176359321)
          ·
            refine ⟨17328160546399047132269491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23104214061865396176359321 17328160546399047132269491)
            ·
              refine ⟨25992240819598570698404237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17328160546399047132269491 25992240819598570698404237)
              ·
                refine ⟨9747090307349464011901589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25992240819598570698404237 9747090307349464011901589)
                ·
                  refine ⟨456894858157006125557887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9747090307349464011901589 456894858157006125557887)
                  ·
                    rfl

theorem cell23_8008196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_8008196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008196 prefixEnd_8008196 := by exact prefixLift 8008196
  have htrace : WordTrace (prefixWord ++ tailWord_8008196) baseStart_8008196 baseEnd_8008196 := by
    simpa [prefixWord, tailWord_8008196, baseEnd_8008196] using wordTrace_append hprefix tailTrace_8008196
  have hstable : (prefixWord ++ tailWord_8008196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008196).length < 2 ^ (prefixWord ++ tailWord_8008196).sum := by decide
  have hdescent : baseEnd_8008196 < baseStart_8008196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008209 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 1, 5]
def baseStart_8008209 : Nat := 118140960795 + 8008209 * 2 ^ 59
def prefixEnd_8008209 : Nat := 4983230072969 + 3 ^ 40 * 8008209 * 2
def baseEnd_8008209 : Nat := 1370686799553854526386141

theorem tailTrace_8008209 : CollatzResearch.WordTrace tailWord_8008209 prefixEnd_8008209 1370686799553854526386141 := by
  unfold tailWord_8008209
  simp only [CollatzResearch.WordTrace]
  refine ⟨292083377844633961054691681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194722251896422640703127787 292083377844633961054691681)
  ·
    refine ⟨219062533383475470791018761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292083377844633961054691681 219062533383475470791018761)
    ·
      refine ⟨164296900037606603093264071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219062533383475470791018761 164296900037606603093264071)
      ·
        refine ⟨246445350056409904639896107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164296900037606603093264071 246445350056409904639896107)
        ·
          refine ⟨369668025084614856959844161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246445350056409904639896107 369668025084614856959844161)
          ·
            refine ⟨277251018813461142719883121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369668025084614856959844161 277251018813461142719883121)
            ·
              refine ⟨207938264110095857039912341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277251018813461142719883121 207938264110095857039912341)
              ·
                refine ⟨9747106130160743298745891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207938264110095857039912341 9747106130160743298745891)
                ·
                  refine ⟨14620659195241114948118837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9747106130160743298745891 14620659195241114948118837)
                  ·
                    refine ⟨1370686799553854526386141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14620659195241114948118837 1370686799553854526386141)
                    ·
                      rfl

theorem cell23_8008209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_8008209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008209 prefixEnd_8008209 := by exact prefixLift 8008209
  have htrace : WordTrace (prefixWord ++ tailWord_8008209) baseStart_8008209 baseEnd_8008209 := by
    simpa [prefixWord, tailWord_8008209, baseEnd_8008209] using wordTrace_append hprefix tailTrace_8008209
  have hstable : (prefixWord ++ tailWord_8008209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008209).length < 2 ^ (prefixWord ++ tailWord_8008209).sum := by decide
  have hdescent : baseEnd_8008209 < baseStart_8008209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008223 : List Nat := [1, 1, 2, 4, 1, 1, 1, 7, 1, 1, 3]
def baseStart_8008223 : Nat := 118140960795 + 8008223 * 2 ^ 59
def prefixEnd_8008223 : Nat := 4983230072969 + 3 ^ 40 * 8008223 * 2
def baseEnd_8008223 : Nat := 4112067587390726524383359

theorem tailTrace_8008223 : CollatzResearch.WordTrace tailWord_8008223 prefixEnd_8008223 4112067587390726524383359 := by
  unfold tailWord_8008223
  simp only [CollatzResearch.WordTrace]
  refine ⟨292083888466583241445701323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194722592311055494297134215 292083888466583241445701323)
  ·
    refine ⟨438125832699874862168551985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292083888466583241445701323 438125832699874862168551985)
    ·
      refine ⟨328594374524906146626413989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438125832699874862168551985 328594374524906146626413989)
      ·
        refine ⟨61611445223419902492452623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328594374524906146626413989 61611445223419902492452623)
        ·
          refine ⟨92417167835129853738678935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61611445223419902492452623 92417167835129853738678935)
          ·
            refine ⟨138625751752694780608018403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92417167835129853738678935 138625751752694780608018403)
            ·
              refine ⟨207938627629042170912027605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138625751752694780608018403 207938627629042170912027605)
              ·
                refine ⟨4873561585055675880750647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207938627629042170912027605 4873561585055675880750647)
                ·
                  refine ⟨7310342377583513821125971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873561585055675880750647 7310342377583513821125971)
                  ·
                    refine ⟨10965513566375270731688957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7310342377583513821125971 10965513566375270731688957)
                    ·
                      refine ⟨4112067587390726524383359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965513566375270731688957 4112067587390726524383359)
                      ·
                        rfl

theorem cell23_8008223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_8008223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008223 prefixEnd_8008223 := by exact prefixLift 8008223
  have htrace : WordTrace (prefixWord ++ tailWord_8008223) baseStart_8008223 baseEnd_8008223 := by
    simpa [prefixWord, tailWord_8008223, baseEnd_8008223] using wordTrace_append hprefix tailTrace_8008223
  have hstable : (prefixWord ++ tailWord_8008223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008223).length < 2 ^ (prefixWord ++ tailWord_8008223).sum := by decide
  have hdescent : baseEnd_8008223 < baseStart_8008223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008240 : List Nat := [2, 1, 1, 1, 2, 3, 6, 2, 1, 1, 3]
def baseStart_8008240 : Nat := 118140960795 + 8008240 * 2 ^ 59
def prefixEnd_8008240 : Nat := 4983230072969 + 3 ^ 40 * 8008240 * 2
def baseEnd_8008240 : Nat := 4112076316561852957870781

theorem tailTrace_8008240 : CollatzResearch.WordTrace tailWord_8008240 prefixEnd_8008240 4112076316561852957870781 := by
  unfold tailWord_8008240
  simp only [CollatzResearch.WordTrace]
  refine ⟨146042254253760826674535087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194723005671681102232713449 146042254253760826674535087)
  ·
    refine ⟨219063381380641240011802631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146042254253760826674535087 219063381380641240011802631)
    ·
      refine ⟨328595072070961860017703947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219063381380641240011802631 328595072070961860017703947)
      ·
        refine ⟨492892608106442790026555921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328595072070961860017703947 492892608106442790026555921)
        ·
          refine ⟨369669456079832092519916941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492892608106442790026555921 369669456079832092519916941)
          ·
            refine ⟨138626046029937034694968853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369669456079832092519916941 138626046029937034694968853)
            ·
              refine ⟨6498095907653298501326665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138626046029937034694968853 6498095907653298501326665)
              ·
                refine ⟨4873571930739973875994999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498095907653298501326665 4873571930739973875994999)
                ·
                  refine ⟨7310357896109960813992499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873571930739973875994999 7310357896109960813992499)
                  ·
                    refine ⟨10965536844164941220988749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7310357896109960813992499 10965536844164941220988749)
                    ·
                      refine ⟨4112076316561852957870781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965536844164941220988749 4112076316561852957870781)
                      ·
                        rfl

theorem cell23_8008240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 1, 3].length) (baseStart_8008240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008240 prefixEnd_8008240 := by exact prefixLift 8008240
  have htrace : WordTrace (prefixWord ++ tailWord_8008240) baseStart_8008240 baseEnd_8008240 := by
    simpa [prefixWord, tailWord_8008240, baseEnd_8008240] using wordTrace_append hprefix tailTrace_8008240
  have hstable : (prefixWord ++ tailWord_8008240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008240).length < 2 ^ (prefixWord ++ tailWord_8008240).sum := by decide
  have hdescent : baseEnd_8008240 < baseStart_8008240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008249 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_8008249 : Nat := 118140960795 + 8008249 * 2 ^ 59
def prefixEnd_8008249 : Nat := 4983230072969 + 3 ^ 40 * 8008249 * 2
def baseEnd_8008249 : Nat := 4112080937887743422658239

theorem tailTrace_8008249 : CollatzResearch.WordTrace tailWord_8008249 prefixEnd_8008249 4112080937887743422658239 := by
  unfold tailWord_8008249
  simp only [CollatzResearch.WordTrace]
  refine ⟨292084836764489047886147801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194723224509659365257431867 292084836764489047886147801)
  ·
    refine ⟨219063627573366785914610851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292084836764489047886147801 219063627573366785914610851)
    ·
      refine ⟨328595441360050178871916277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219063627573366785914610851 328595441360050178871916277)
      ·
        refine ⟨30805822627504704269242151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328595441360050178871916277 30805822627504704269242151)
        ·
          refine ⟨46208733941257056403863227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30805822627504704269242151 46208733941257056403863227)
          ·
            refine ⟨69313100911885584605794841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46208733941257056403863227 69313100911885584605794841)
            ·
              refine ⟨51984825683914188454346131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69313100911885584605794841 51984825683914188454346131)
              ·
                refine ⟨77977238525871282681519197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51984825683914188454346131 77977238525871282681519197)
                ·
                  refine ⟨29241464447201731005569699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77977238525871282681519197 29241464447201731005569699)
                  ·
                    refine ⟨43862196670802596508354549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29241464447201731005569699 43862196670802596508354549)
                    ·
                      refine ⟨4112080937887743422658239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43862196670802596508354549 4112080937887743422658239)
                      ·
                        rfl

theorem cell23_8008249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_8008249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008249 prefixEnd_8008249 := by exact prefixLift 8008249
  have htrace : WordTrace (prefixWord ++ tailWord_8008249) baseStart_8008249 baseEnd_8008249 := by
    simpa [prefixWord, tailWord_8008249, baseEnd_8008249] using wordTrace_append hprefix tailTrace_8008249
  have hstable : (prefixWord ++ tailWord_8008249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008249).length < 2 ^ (prefixWord ++ tailWord_8008249).sum := by decide
  have hdescent : baseEnd_8008249 < baseStart_8008249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008256 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 2, 4]
def baseStart_8008256 : Nat := 118140960795 + 8008256 * 2 ^ 59
def prefixEnd_8008256 : Nat := 4983230072969 + 3 ^ 40 * 8008256 * 2
def baseEnd_8008256 : Nat := 1370694844084108298423569

theorem tailTrace_8008256 : CollatzResearch.WordTrace tailWord_8008256 prefixEnd_8008256 1370694844084108298423569 := by
  unfold tailWord_8008256
  simp only [CollatzResearch.WordTrace]
  refine ⟨146042546037731844040826311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194723394716975792054435081 146042546037731844040826311)
  ·
    refine ⟨219063819056597766061239467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146042546037731844040826311 219063819056597766061239467)
    ·
      refine ⟨328595728584896649091859201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219063819056597766061239467 328595728584896649091859201)
      ·
        refine ⟨246446796438672486818894401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328595728584896649091859201 246446796438672486818894401)
        ·
          refine ⟨184835097329004365114170801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246446796438672486818894401 184835097329004365114170801)
          ·
            refine ⟨138626322996753273835628101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184835097329004365114170801 138626322996753273835628101)
            ·
              refine ⟨25992435561891238844180269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138626322996753273835628101 25992435561891238844180269)
              ·
                refine ⟨9747163335709214566567601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25992435561891238844180269 9747163335709214566567601)
                ·
                  refine ⟨7310372501781910924925701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9747163335709214566567601 7310372501781910924925701)
                  ·
                    refine ⟨1370694844084108298423569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7310372501781910924925701 1370694844084108298423569)
                    ·
                      rfl

theorem cell23_8008256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 4].length) (baseStart_8008256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008256 prefixEnd_8008256 := by exact prefixLift 8008256
  have htrace : WordTrace (prefixWord ++ tailWord_8008256) baseStart_8008256 baseEnd_8008256 := by
    simpa [prefixWord, tailWord_8008256, baseEnd_8008256] using wordTrace_append hprefix tailTrace_8008256
  have hstable : (prefixWord ++ tailWord_8008256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008256).length < 2 ^ (prefixWord ++ tailWord_8008256).sum := by decide
  have hdescent : baseEnd_8008256 < baseStart_8008256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008263 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_8008263 : Nat := 118140960795 + 8008263 * 2 ^ 59
def prefixEnd_8008263 : Nat := 4983230072969 + 3 ^ 40 * 8008263 * 2
def baseEnd_8008263 : Nat := 4112088126616906367883175

theorem tailTrace_8008263 : CollatzResearch.WordTrace tailWord_8008263 prefixEnd_8008263 4112088126616906367883175 := by
  unfold tailWord_8008263
  simp only [CollatzResearch.WordTrace]
  refine ⟨292085347386438328277157443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194723564924292218851438295 292085347386438328277157443)
  ·
    refine ⟨438128021079657492415736165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292085347386438328277157443 438128021079657492415736165)
    ·
      refine ⟨82149003952435779827950531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438128021079657492415736165 82149003952435779827950531)
      ·
        refine ⟨123223505928653669741925797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82149003952435779827950531 123223505928653669741925797)
        ·
          refine ⟨23104407361622563076611087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123223505928653669741925797 23104407361622563076611087)
          ·
            refine ⟨34656611042433844614916631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23104407361622563076611087 34656611042433844614916631)
            ·
              refine ⟨51984916563650766922374947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34656611042433844614916631 51984916563650766922374947)
              ·
                refine ⟨77977374845476150383562421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51984916563650766922374947 77977374845476150383562421)
                ·
                  refine ⟨7310378891763389098458977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77977374845476150383562421 7310378891763389098458977)
                  ·
                    refine ⟨5482784168822541823844233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7310378891763389098458977 5482784168822541823844233)
                    ·
                      refine ⟨4112088126616906367883175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482784168822541823844233 4112088126616906367883175)
                      ·
                        rfl

theorem cell23_8008263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_8008263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008263 prefixEnd_8008263 := by exact prefixLift 8008263
  have htrace : WordTrace (prefixWord ++ tailWord_8008263) baseStart_8008263 baseEnd_8008263 := by
    simpa [prefixWord, tailWord_8008263, baseEnd_8008263] using wordTrace_append hprefix tailTrace_8008263
  have hstable : (prefixWord ++ tailWord_8008263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008263).length < 2 ^ (prefixWord ++ tailWord_8008263).sum := by decide
  have hdescent : baseEnd_8008263 < baseStart_8008263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008266 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_8008266 : Nat := 118140960795 + 8008266 * 2 ^ 59
def prefixEnd_8008266 : Nat := 4983230072969 + 3 ^ 40 * 8008266 * 2
def baseEnd_8008266 : Nat := 4112089667058869856145661

theorem tailTrace_8008266 : CollatzResearch.WordTrace tailWord_8008266 prefixEnd_8008266 4112089667058869856145661 := by
  unfold tailWord_8008266
  simp only [CollatzResearch.WordTrace]
  refine ⟨73021364201356864947379163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194723637870284973193011101 73021364201356864947379163)
  ·
    refine ⟨109532046302035297421068745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73021364201356864947379163 109532046302035297421068745)
    ·
      refine ⟨82149034726526473065801559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109532046302035297421068745 82149034726526473065801559)
      ·
        refine ⟨123223552089789709598702339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82149034726526473065801559 123223552089789709598702339)
        ·
          refine ⟨184835328134684564398053509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123223552089789709598702339 184835328134684564398053509)
          ·
            refine ⟨34656624025253355824635033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184835328134684564398053509 34656624025253355824635033)
            ·
              refine ⟨25992468018940016868476275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34656624025253355824635033 25992468018940016868476275)
              ·
                refine ⟨38988702028410025302714413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25992468018940016868476275 38988702028410025302714413)
                ·
                  refine ⟨14620763260653759488517905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38988702028410025302714413 14620763260653759488517905)
                  ·
                    refine ⟨10965572445490319616388429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14620763260653759488517905 10965572445490319616388429)
                    ·
                      refine ⟨4112089667058869856145661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965572445490319616388429 4112089667058869856145661)
                      ·
                        rfl

theorem cell23_8008266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_8008266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008266 prefixEnd_8008266 := by exact prefixLift 8008266
  have htrace : WordTrace (prefixWord ++ tailWord_8008266) baseStart_8008266 baseEnd_8008266 := by
    simpa [prefixWord, tailWord_8008266, baseEnd_8008266] using wordTrace_append hprefix tailTrace_8008266
  have hstable : (prefixWord ++ tailWord_8008266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008266).length < 2 ^ (prefixWord ++ tailWord_8008266).sum := by decide
  have hdescent : baseEnd_8008266 < baseStart_8008266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008276 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_8008276 : Nat := 118140960795 + 8008276 * 2 ^ 59
def prefixEnd_8008276 : Nat := 4983230072969 + 3 ^ 40 * 8008276 * 2
def baseEnd_8008276 : Nat := 4112094801865414817020615

theorem tailTrace_8008276 : CollatzResearch.WordTrace tailWord_8008276 prefixEnd_8008276 4112094801865414817020615 := by
  unfold tailWord_8008276
  simp only [CollatzResearch.WordTrace]
  refine ⟨146042910767695615748690341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194723881023594154331587121 146042910767695615748690341)
  ·
    refine ⟨27383045768942927952879439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146042910767695615748690341 27383045768942927952879439)
    ·
      refine ⟨41074568653414391929319159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27383045768942927952879439 41074568653414391929319159)
      ·
        refine ⟨61611852980121587893978739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41074568653414391929319159 61611852980121587893978739)
        ·
          refine ⟨92417779470182381840968109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61611852980121587893978739 92417779470182381840968109)
          ·
            refine ⟨34656667301318393190363041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92417779470182381840968109 34656667301318393190363041)
            ·
              refine ⟨25992500475988794892772281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34656667301318393190363041 25992500475988794892772281)
              ·
                refine ⟨19494375356991596169579211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25992500475988794892772281 19494375356991596169579211)
                ·
                  refine ⟨29241563035487394254368817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19494375356991596169579211 29241563035487394254368817)
                  ·
                    refine ⟨21931172276615545690776613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29241563035487394254368817 21931172276615545690776613)
                    ·
                      refine ⟨4112094801865414817020615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21931172276615545690776613 4112094801865414817020615)
                      ·
                        rfl

theorem cell23_8008276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_8008276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008276 prefixEnd_8008276 := by exact prefixLift 8008276
  have htrace : WordTrace (prefixWord ++ tailWord_8008276) baseStart_8008276 baseEnd_8008276 := by
    simpa [prefixWord, tailWord_8008276, baseEnd_8008276] using wordTrace_append hprefix tailTrace_8008276
  have hstable : (prefixWord ++ tailWord_8008276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008276).length < 2 ^ (prefixWord ++ tailWord_8008276).sum := by decide
  have hdescent : baseEnd_8008276 < baseStart_8008276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008280 : List Nat := [2, 1, 2, 2, 1, 2, 3, 5, 1, 2, 2]
def baseStart_8008280 : Nat := 118140960795 + 8008280 * 2 ^ 59
def prefixEnd_8008280 : Nat := 4983230072969 + 3 ^ 40 * 8008280 * 2
def baseEnd_8008280 : Nat := 4112096855788032801370597

theorem tailTrace_8008280 : CollatzResearch.WordTrace tailWord_8008280 prefixEnd_8008280 4112096855788032801370597 := by
  unfold tailWord_8008280
  simp only [CollatzResearch.WordTrace]
  refine ⟨146042983713688370090263147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194723978284917826787017529 146042983713688370090263147)
  ·
    refine ⟨219064475570532555135394721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146042983713688370090263147 219064475570532555135394721)
    ·
      refine ⟨164298356677899416351546041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219064475570532555135394721 164298356677899416351546041)
      ·
        refine ⟨123223767508424562263659531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164298356677899416351546041 123223767508424562263659531)
        ·
          refine ⟨184835651262636843395489297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123223767508424562263659531 184835651262636843395489297)
          ·
            refine ⟨138626738446977632546616973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184835651262636843395489297 138626738446977632546616973)
            ·
              refine ⟨51985026917616612204981365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138626738446977632546616973 51985026917616612204981365)
              ·
                refine ⟨4873596273526557394217003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51985026917616612204981365 4873596273526557394217003)
                ·
                  refine ⟨7310394410289836091325505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873596273526557394217003 7310394410289836091325505)
                  ·
                    refine ⟨5482795807717377068494129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7310394410289836091325505 5482795807717377068494129)
                    ·
                      refine ⟨4112096855788032801370597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482795807717377068494129 4112096855788032801370597)
                      ·
                        rfl

theorem cell23_8008280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_8008280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008280 prefixEnd_8008280 := by exact prefixLift 8008280
  have htrace : WordTrace (prefixWord ++ tailWord_8008280) baseStart_8008280 baseEnd_8008280 := by
    simpa [prefixWord, tailWord_8008280, baseEnd_8008280] using wordTrace_append hprefix tailTrace_8008280
  have hstable : (prefixWord ++ tailWord_8008280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008280).length < 2 ^ (prefixWord ++ tailWord_8008280).sum := by decide
  have hdescent : baseEnd_8008280 < baseStart_8008280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008290 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_8008290 : Nat := 118140960795 + 8008290 * 2 ^ 59
def prefixEnd_8008290 : Nat := 4983230072969 + 3 ^ 40 * 8008290 * 2
def baseEnd_8008290 : Nat := 1370700663531525920748517

theorem tailTrace_8008290 : CollatzResearch.WordTrace tailWord_8008290 prefixEnd_8008290 1370700663531525920748517 := by
  unfold tailWord_8008290
  simp only [CollatzResearch.WordTrace]
  refine ⟨73021583039335127972097581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194724221438227007925593549 73021583039335127972097581)
  ·
    refine ⟨27383093639750672989536593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73021583039335127972097581 27383093639750672989536593)
    ·
      refine ⟨20537320229813004742152445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27383093639750672989536593 20537320229813004742152445)
      ·
        refine ⟨7701495086179876778307167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20537320229813004742152445 7701495086179876778307167)
        ·
          refine ⟨11552242629269815167460751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701495086179876778307167 11552242629269815167460751)
          ·
            refine ⟨17328363943904722751191127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552242629269815167460751 17328363943904722751191127)
            ·
              refine ⟨25992545915857084126786691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17328363943904722751191127 25992545915857084126786691)
              ·
                refine ⟨38988818873785626190180037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25992545915857084126786691 38988818873785626190180037)
                ·
                  refine ⟨7310403538834804910658757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38988818873785626190180037 7310403538834804910658757)
                  ·
                    refine ⟨1370700663531525920748517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7310403538834804910658757 1370700663531525920748517)
                    ·
                      rfl

theorem cell23_8008290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_8008290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008290 prefixEnd_8008290 := by exact prefixLift 8008290
  have htrace : WordTrace (prefixWord ++ tailWord_8008290) baseStart_8008290 baseEnd_8008290 := by
    simpa [prefixWord, tailWord_8008290, baseEnd_8008290] using wordTrace_append hprefix tailTrace_8008290
  have hstable : (prefixWord ++ tailWord_8008290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008290).length < 2 ^ (prefixWord ++ tailWord_8008290).sum := by decide
  have hdescent : baseEnd_8008290 < baseStart_8008290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008310 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_8008310 : Nat := 118140960795 + 8008310 * 2 ^ 59
def prefixEnd_8008310 : Nat := 4983230072969 + 3 ^ 40 * 8008310 * 2
def baseEnd_8008310 : Nat := 4112112260207667683995459

theorem tailTrace_8008310 : CollatzResearch.WordTrace tailWord_8008310 prefixEnd_8008310 4112112260207667683995459 := by
  unfold tailWord_8008310
  simp only [CollatzResearch.WordTrace]
  refine ⟨18255441351079253456507399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194724707744845370202745589 18255441351079253456507399)
  ·
    refine ⟨27383162026618880184761099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18255441351079253456507399 27383162026618880184761099)
    ·
      refine ⟨41074743039928320277141649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27383162026618880184761099 41074743039928320277141649)
      ·
        refine ⟨30806057279946240207856237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41074743039928320277141649 30806057279946240207856237)
        ·
          refine ⟨11552271479979840077946089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30806057279946240207856237 11552271479979840077946089)
          ·
            refine ⟨8664203609984880058459567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11552271479979840077946089 8664203609984880058459567)
            ·
              refine ⟨12996305414977320087689351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8664203609984880058459567 12996305414977320087689351)
              ·
                refine ⟨19494458122465980131534027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12996305414977320087689351 19494458122465980131534027)
                ·
                  refine ⟨29241687183698970197301041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19494458122465980131534027 29241687183698970197301041)
                  ·
                    refine ⟨21931265387774227647975781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29241687183698970197301041 21931265387774227647975781)
                    ·
                      refine ⟨4112112260207667683995459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21931265387774227647975781 4112112260207667683995459)
                      ·
                        rfl

theorem cell23_8008310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_8008310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008310 prefixEnd_8008310 := by exact prefixLift 8008310
  have htrace : WordTrace (prefixWord ++ tailWord_8008310) baseStart_8008310 baseEnd_8008310 := by
    simpa [prefixWord, tailWord_8008310, baseEnd_8008310] using wordTrace_append hprefix tailTrace_8008310
  have hstable : (prefixWord ++ tailWord_8008310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008310).length < 2 ^ (prefixWord ++ tailWord_8008310).sum := by decide
  have hdescent : baseEnd_8008310 < baseStart_8008310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008313 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 3]
def baseStart_8008313 : Nat := 118140960795 + 8008313 * 2 ^ 59
def prefixEnd_8008313 : Nat := 4983230072969 + 3 ^ 40 * 8008313 * 2
def baseEnd_8008313 : Nat := 4112113800649631172257945

theorem tailTrace_8008313 : CollatzResearch.WordTrace tailWord_8008313 prefixEnd_8008313 4112113800649631172257945 := by
  unfold tailWord_8008313
  simp only [CollatzResearch.WordTrace]
  refine ⟨292087171036257186816477593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194724780690838124544318395 292087171036257186816477593)
  ·
    refine ⟨219065378277192890112358195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292087171036257186816477593 219065378277192890112358195)
    ·
      refine ⟨328598067415789335168537293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219065378277192890112358195 328598067415789335168537293)
      ·
        refine ⟨123224275280921000688201485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328598067415789335168537293 123224275280921000688201485)
        ·
          refine ⟨46209103230345375258075557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123224275280921000688201485 46209103230345375258075557)
          ·
            refine ⟨8664206855689757860889167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46209103230345375258075557 8664206855689757860889167)
            ·
              refine ⟨12996310283534636791333751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8664206855689757860889167 12996310283534636791333751)
              ·
                refine ⟨19494465425301955187000627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12996310283534636791333751 19494465425301955187000627)
                ·
                  refine ⟨29241698137952932780500941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19494465425301955187000627 29241698137952932780500941)
                  ·
                    refine ⟨10965636801732349792687853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29241698137952932780500941 10965636801732349792687853)
                    ·
                      refine ⟨4112113800649631172257945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965636801732349792687853 4112113800649631172257945)
                      ·
                        rfl

theorem cell23_8008313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_8008313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008313 prefixEnd_8008313 := by exact prefixLift 8008313
  have htrace : WordTrace (prefixWord ++ tailWord_8008313) baseStart_8008313 baseEnd_8008313 := by
    simpa [prefixWord, tailWord_8008313, baseEnd_8008313] using wordTrace_append hprefix tailTrace_8008313
  have hstable : (prefixWord ++ tailWord_8008313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008313).length < 2 ^ (prefixWord ++ tailWord_8008313).sum := by decide
  have hdescent : baseEnd_8008313 < baseStart_8008313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008323 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 1, 3, 2]
def baseStart_8008323 : Nat := 118140960795 + 8008323 * 2 ^ 59
def prefixEnd_8008323 : Nat := 4983230072969 + 3 ^ 40 * 8008323 * 2
def baseEnd_8008323 : Nat := 4112118935456176133132899

theorem tailTrace_8008323 : CollatzResearch.WordTrace tailWord_8008323 prefixEnd_8008323 4112118935456176133132899 := by
  unfold tailWord_8008323
  simp only [CollatzResearch.WordTrace]
  refine ⟨292087535766220958524341623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194725023844147305682894415 292087535766220958524341623)
  ·
    refine ⟨438131303649331437786512435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292087535766220958524341623 438131303649331437786512435)
    ·
      refine ⟨657196955473997156679768653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438131303649331437786512435 657196955473997156679768653)
      ·
        refine ⟨246448858302748933754913245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 657196955473997156679768653 246448858302748933754913245)
        ·
          refine ⟨92418321863530850158092467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246448858302748933754913245 92418321863530850158092467)
          ·
            refine ⟨138627482795296275237138701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92418321863530850158092467 138627482795296275237138701)
            ·
              refine ⟨51985306048236103213927013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138627482795296275237138701 51985306048236103213927013)
              ·
                refine ⟨9747244884044269352611315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51985306048236103213927013 9747244884044269352611315)
                ·
                  refine ⟨14620867326066404028916973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9747244884044269352611315 14620867326066404028916973)
                  ·
                    refine ⟨5482825247274901510843865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14620867326066404028916973 5482825247274901510843865)
                    ·
                      refine ⟨4112118935456176133132899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482825247274901510843865 4112118935456176133132899)
                      ·
                        rfl

theorem cell23_8008323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_8008323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008323 prefixEnd_8008323 := by exact prefixLift 8008323
  have htrace : WordTrace (prefixWord ++ tailWord_8008323) baseStart_8008323 baseEnd_8008323 := by
    simpa [prefixWord, tailWord_8008323, baseEnd_8008323] using wordTrace_append hprefix tailTrace_8008323
  have hstable : (prefixWord ++ tailWord_8008323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008323).length < 2 ^ (prefixWord ++ tailWord_8008323).sum := by decide
  have hdescent : baseEnd_8008323 < baseStart_8008323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008339 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 5]
def baseStart_8008339 : Nat := 118140960795 + 8008339 * 2 ^ 59
def prefixEnd_8008339 : Nat := 4983230072969 + 3 ^ 40 * 8008339 * 2
def baseEnd_8008339 : Nat := 4112127151146648070532825

theorem tailTrace_8008339 : CollatzResearch.WordTrace tailWord_8008339 prefixEnd_8008339 4112127151146648070532825 := by
  unfold tailWord_8008339
  simp only [CollatzResearch.WordTrace]
  refine ⟨292088119334162993256924071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194725412889441995504616047 292088119334162993256924071)
  ·
    refine ⟨438132179001244489885386107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292088119334162993256924071 438132179001244489885386107)
    ·
      refine ⟨657198268501866734828079161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438132179001244489885386107 657198268501866734828079161)
      ·
        refine ⟨492898701376400051121059371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657198268501866734828079161 492898701376400051121059371)
        ·
          refine ⟨739348052064600076681589057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492898701376400051121059371 739348052064600076681589057)
          ·
            refine ⟨554511039048450057511191793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739348052064600076681589057 554511039048450057511191793)
            ·
              refine ⟨415883279286337543133393845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554511039048450057511191793 415883279286337543133393845)
              ·
                refine ⟨38989057433094144668755673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 415883279286337543133393845 38989057433094144668755673)
                ·
                  refine ⟨29241793074820608501566755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38989057433094144668755673 29241793074820608501566755)
                  ·
                    refine ⟨43862689612230912752350133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29241793074820608501566755 43862689612230912752350133)
                    ·
                      refine ⟨4112127151146648070532825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43862689612230912752350133 4112127151146648070532825)
                      ·
                        rfl

theorem cell23_8008339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_8008339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008339 prefixEnd_8008339 := by exact prefixLift 8008339
  have htrace : WordTrace (prefixWord ++ tailWord_8008339) baseStart_8008339 baseEnd_8008339 := by
    simpa [prefixWord, tailWord_8008339, baseEnd_8008339] using wordTrace_append hprefix tailTrace_8008339
  have hstable : (prefixWord ++ tailWord_8008339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008339).length < 2 ^ (prefixWord ++ tailWord_8008339).sum := by decide
  have hdescent : baseEnd_8008339 < baseStart_8008339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008356 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_8008356 : Nat := 118140960795 + 8008356 * 2 ^ 59
def prefixEnd_8008356 : Nat := 4983230072969 + 3 ^ 40 * 8008356 * 2
def baseEnd_8008356 : Nat := 4112135880317774504020247

theorem tailTrace_8008356 : CollatzResearch.WordTrace tailWord_8008356 prefixEnd_8008356 4112135880317774504020247 := by
  unfold tailWord_8008356
  simp only [CollatzResearch.WordTrace]
  refine ⟨146044369687550702580146461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194725826250067603440195281 146044369687550702580146461)
  ·
    refine ⟨54766638632831513467554923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146044369687550702580146461 54766638632831513467554923)
    ·
      refine ⟨82149957949247270201332385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54766638632831513467554923 82149957949247270201332385)
      ·
        refine ⟨61612468461935452650999289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82149957949247270201332385 61612468461935452650999289)
        ·
          refine ⟨46209351346451589488249467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61612468461935452650999289 46209351346451589488249467)
          ·
            refine ⟨69314027019677384232374201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46209351346451589488249467 69314027019677384232374201)
            ·
              refine ⟨51985520264758038174280651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69314027019677384232374201 51985520264758038174280651)
              ·
                refine ⟨77978280397137057261420977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51985520264758038174280651 77978280397137057261420977)
                ·
                  refine ⟨58483710297852792946065733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77978280397137057261420977 58483710297852792946065733)
                  ·
                    refine ⟨10965695680847398677387325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58483710297852792946065733 10965695680847398677387325)
                    ·
                      refine ⟨4112135880317774504020247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965695680847398677387325 4112135880317774504020247)
                      ·
                        rfl

theorem cell23_8008356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_8008356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008356 prefixEnd_8008356 := by exact prefixLift 8008356
  have htrace : WordTrace (prefixWord ++ tailWord_8008356) baseStart_8008356 baseEnd_8008356 := by
    simpa [prefixWord, tailWord_8008356, baseEnd_8008356] using wordTrace_append hprefix tailTrace_8008356
  have hstable : (prefixWord ++ tailWord_8008356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008356).length < 2 ^ (prefixWord ++ tailWord_8008356).sum := by decide
  have hdescent : baseEnd_8008356 < baseStart_8008356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008404 : List Nat := [2, 4, 1, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_8008404 : Nat := 118140960795 + 8008404 * 2 ^ 59
def prefixEnd_8008404 : Nat := 4983230072969 + 3 ^ 40 * 8008404 * 2
def baseEnd_8008404 : Nat := 4112160527389190316220027

theorem tailTrace_8008404 : CollatzResearch.WordTrace tailWord_8008404 prefixEnd_8008404 4112160527389190316220027 := by
  unfold tailWord_8008404
  simp only [CollatzResearch.WordTrace]
  refine ⟨146045245039463754679020133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194726993385951672905360177 146045245039463754679020133)
  ·
    refine ⟨27383483444899454002316275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146045245039463754679020133 27383483444899454002316275)
    ·
      refine ⟨41075225167349181003474413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27383483444899454002316275 41075225167349181003474413)
      ·
        refine ⟨15403209437755942876302905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41075225167349181003474413 15403209437755942876302905)
        ·
          refine ⟨11552407078316957157227179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15403209437755942876302905 11552407078316957157227179)
          ·
            refine ⟨17328610617475435735840769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552407078316957157227179 17328610617475435735840769)
            ·
              refine ⟨12996457963106576801880577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17328610617475435735840769 12996457963106576801880577)
              ·
                refine ⟨9747343472329932601410433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12996457963106576801880577 9747343472329932601410433)
                ·
                  refine ⟨7310507604247449451057825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9747343472329932601410433 7310507604247449451057825)
                  ·
                    refine ⟨5482880703185587088293369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7310507604247449451057825 5482880703185587088293369)
                    ·
                      refine ⟨4112160527389190316220027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482880703185587088293369 4112160527389190316220027)
                      ·
                        rfl

theorem cell23_8008404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_8008404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008404 prefixEnd_8008404 := by exact prefixLift 8008404
  have htrace : WordTrace (prefixWord ++ tailWord_8008404) baseStart_8008404 baseEnd_8008404 := by
    simpa [prefixWord, tailWord_8008404, baseEnd_8008404] using wordTrace_append hprefix tailTrace_8008404
  have hstable : (prefixWord ++ tailWord_8008404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008404).length < 2 ^ (prefixWord ++ tailWord_8008404).sum := by decide
  have hdescent : baseEnd_8008404 < baseStart_8008404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008426 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_8008426 : Nat := 118140960795 + 8008426 * 2 ^ 59
def prefixEnd_8008426 : Nat := 4983230072969 + 3 ^ 40 * 8008426 * 2
def baseEnd_8008426 : Nat := 4112171823963589230144925

theorem tailTrace_8008426 : CollatzResearch.WordTrace tailWord_8008426 prefixEnd_8008426 4112171823963589230144925 := by
  unfold tailWord_8008426
  simp only [CollatzResearch.WordTrace]
  refine ⟨73022823121211951778835283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194727528323231871410227421 73022823121211951778835283)
  ·
    refine ⟨109534234681817927668252925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73022823121211951778835283 109534234681817927668252925)
    ·
      refine ⟨41075338005681722875594847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109534234681817927668252925 41075338005681722875594847)
      ·
        refine ⟨61613007008522584313392271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41075338005681722875594847 61613007008522584313392271)
        ·
          refine ⟨92419510512783876470088407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61613007008522584313392271 92419510512783876470088407)
          ·
            refine ⟨138629265769175814705132611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92419510512783876470088407 138629265769175814705132611)
            ·
              refine ⟨207943898653763722057698917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138629265769175814705132611 207943898653763722057698917)
              ·
                refine ⟨38989480997580697885818547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207943898653763722057698917 38989480997580697885818547)
                ·
                  refine ⟨58484221496371046828727821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38989480997580697885818547 58484221496371046828727821)
                  ·
                    refine ⟨21931583061139142560772933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58484221496371046828727821 21931583061139142560772933)
                    ·
                      refine ⟨4112171823963589230144925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21931583061139142560772933 4112171823963589230144925)
                      ·
                        rfl

theorem cell23_8008426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_8008426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008426 prefixEnd_8008426 := by exact prefixLift 8008426
  have htrace : WordTrace (prefixWord ++ tailWord_8008426) baseStart_8008426 baseEnd_8008426 := by
    simpa [prefixWord, tailWord_8008426, baseEnd_8008426] using wordTrace_append hprefix tailTrace_8008426
  have hstable : (prefixWord ++ tailWord_8008426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008426).length < 2 ^ (prefixWord ++ tailWord_8008426).sum := by decide
  have hdescent : baseEnd_8008426 < baseStart_8008426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008456 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_8008456 : Nat := 118140960795 + 8008456 * 2 ^ 59
def prefixEnd_8008456 : Nat := 4983230072969 + 3 ^ 40 * 8008456 * 2
def baseEnd_8008456 : Nat := 4112187228383224112769787

theorem tailTrace_8008456 : CollatzResearch.WordTrace tailWord_8008456 prefixEnd_8008456 4112187228383224112769787 := by
  unfold tailWord_8008456
  simp only [CollatzResearch.WordTrace]
  refine ⟨146046193337369561119466611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194728257783159414825955481 146046193337369561119466611)
  ·
    refine ⟨219069290006054341679199917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146046193337369561119466611 219069290006054341679199917)
    ·
      refine ⟨82150983752270378129699969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219069290006054341679199917 82150983752270378129699969)
      ·
        refine ⟨61613237814202783597274977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82150983752270378129699969 61613237814202783597274977)
        ·
          refine ⟨46209928360652087697956233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61613237814202783597274977 46209928360652087697956233)
          ·
            refine ⟨34657446270489065773467175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46209928360652087697956233 34657446270489065773467175)
            ·
              refine ⟨51986169405733598660200763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34657446270489065773467175 51986169405733598660200763)
              ·
                refine ⟨77979254108600397990301145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51986169405733598660200763 77979254108600397990301145)
                ·
                  refine ⟨58484440581450298492725859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77979254108600397990301145 58484440581450298492725859)
                  ·
                    refine ⟨87726660872175447739088789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58484440581450298492725859 87726660872175447739088789)
                    ·
                      refine ⟨4112187228383224112769787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87726660872175447739088789 4112187228383224112769787)
                      ·
                        rfl

theorem cell23_8008456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_8008456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008456 prefixEnd_8008456 := by exact prefixLift 8008456
  have htrace : WordTrace (prefixWord ++ tailWord_8008456) baseStart_8008456 baseEnd_8008456 := by
    simpa [prefixWord, tailWord_8008456, baseEnd_8008456] using wordTrace_append hprefix tailTrace_8008456
  have hstable : (prefixWord ++ tailWord_8008456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008456).length < 2 ^ (prefixWord ++ tailWord_8008456).sum := by decide
  have hdescent : baseEnd_8008456 < baseStart_8008456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008496 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 3, 5]
def baseStart_8008496 : Nat := 118140960795 + 8008496 * 2 ^ 59
def prefixEnd_8008496 : Nat := 4983230072969 + 3 ^ 40 * 8008496 * 2
def baseEnd_8008496 : Nat := 1370735922536467985423201

theorem tailTrace_8008496 : CollatzResearch.WordTrace tailWord_8008496 prefixEnd_8008496 1370735922536467985423201 := by
  unfold tailWord_8008496
  simp only [CollatzResearch.WordTrace]
  refine ⟨146046922797297104535194671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194729230396396139380259561 146046922797297104535194671)
  ·
    refine ⟨219070384195945656802792007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146046922797297104535194671 219070384195945656802792007)
    ·
      refine ⟨328605576293918485204188011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219070384195945656802792007 328605576293918485204188011)
      ·
        refine ⟨492908364440877727806282017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328605576293918485204188011 492908364440877727806282017)
        ·
          refine ⟨369681273330658295854711513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492908364440877727806282017 369681273330658295854711513)
          ·
            refine ⟨277260954997993721891033635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369681273330658295854711513 277260954997993721891033635)
            ·
              refine ⟨415891432496990582836550453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277260954997993721891033635 415891432496990582836550453)
              ·
                refine ⟨38989821796592867140926605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 415891432496990582836550453 38989821796592867140926605)
                ·
                  refine ⟨14621183173722325177847477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38989821796592867140926605 14621183173722325177847477)
                  ·
                    refine ⟨1370735922536467985423201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14621183173722325177847477 1370735922536467985423201)
                    ·
                      rfl

theorem cell23_8008496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_8008496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008496 prefixEnd_8008496 := by exact prefixLift 8008496
  have htrace : WordTrace (prefixWord ++ tailWord_8008496) baseStart_8008496 baseEnd_8008496 := by
    simpa [prefixWord, tailWord_8008496, baseEnd_8008496] using wordTrace_append hprefix tailTrace_8008496
  have hstable : (prefixWord ++ tailWord_8008496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008496).length < 2 ^ (prefixWord ++ tailWord_8008496).sum := by decide
  have hdescent : baseEnd_8008496 < baseStart_8008496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008503 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 1, 5, 2]
def baseStart_8008503 : Nat := 118140960795 + 8008503 * 2 ^ 59
def prefixEnd_8008503 : Nat := 4983230072969 + 3 ^ 40 * 8008503 * 2
def baseEnd_8008503 : Nat := 4112211361973985428882071

theorem tailTrace_8008503 : CollatzResearch.WordTrace tailWord_8008503 prefixEnd_8008503 4112211361973985428882071 := by
  unfold tailWord_8008503
  simp only [CollatzResearch.WordTrace]
  refine ⟨292094100905568849265894163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194729400603712566177262775 292094100905568849265894163)
  ·
    refine ⟨438141151358353273898841245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292094100905568849265894163 438141151358353273898841245)
    ·
      refine ⟨164302931759382477712065467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438141151358353273898841245 164302931759382477712065467)
      ·
        refine ⟨246454397639073716568098201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164302931759382477712065467 246454397639073716568098201)
        ·
          refine ⟨184840798229305287426073651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246454397639073716568098201 184840798229305287426073651)
          ·
            refine ⟨277261197343957931139110477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184840798229305287426073651 277261197343957931139110477)
            ·
              refine ⟨103972949003984224177166429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277261197343957931139110477 103972949003984224177166429)
              ·
                refine ⟨38989855876494084066437411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103972949003984224177166429 38989855876494084066437411)
                ·
                  refine ⟨58484783814741126099656117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38989855876494084066437411 58484783814741126099656117)
                  ·
                    refine ⟨5482948482631980571842761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58484783814741126099656117 5482948482631980571842761)
                    ·
                      refine ⟨4112211361973985428882071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482948482631980571842761 4112211361973985428882071)
                      ·
                        rfl

theorem cell23_8008503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_8008503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008503 prefixEnd_8008503 := by exact prefixLift 8008503
  have htrace : WordTrace (prefixWord ++ tailWord_8008503) baseStart_8008503 baseEnd_8008503 := by
    simpa [prefixWord, tailWord_8008503, baseEnd_8008503] using wordTrace_append hprefix tailTrace_8008503
  have hstable : (prefixWord ++ tailWord_8008503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008503).length < 2 ^ (prefixWord ++ tailWord_8008503).sum := by decide
  have hdescent : baseEnd_8008503 < baseStart_8008503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008520 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_8008520 : Nat := 118140960795 + 8008520 * 2 ^ 59
def prefixEnd_8008520 : Nat := 4983230072969 + 3 ^ 40 * 8008520 * 2
def baseEnd_8008520 : Nat := 4112220091145111862369493

theorem tailTrace_8008520 : CollatzResearch.WordTrace tailWord_8008520 prefixEnd_8008520 4112220091145111862369493 := by
  unfold tailWord_8008520
  simp only [CollatzResearch.WordTrace]
  refine ⟨146047360473253630584631507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194729813964338174112842009 146047360473253630584631507)
  ·
    refine ⟨219071040709880445876947261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146047360473253630584631507 219071040709880445876947261)
    ·
      refine ⟨82151640266205167203855223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219071040709880445876947261 82151640266205167203855223)
      ·
        refine ⟨123227460399307750805782835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82151640266205167203855223 123227460399307750805782835)
        ·
          refine ⟨184841190598961626208674253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123227460399307750805782835 184841190598961626208674253)
          ·
            refine ⟨69315446474610609828252845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184841190598961626208674253 69315446474610609828252845)
            ·
              refine ⟨25993292427978978685594817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69315446474610609828252845 25993292427978978685594817)
              ·
                refine ⟨19494969320984234014196113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25993292427978978685594817 19494969320984234014196113)
                ·
                  refine ⟨14621226990738175510647085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19494969320984234014196113 14621226990738175510647085)
                  ·
                    refine ⟨5482960121526815816492657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14621226990738175510647085 5482960121526815816492657)
                    ·
                      refine ⟨4112220091145111862369493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5482960121526815816492657 4112220091145111862369493)
                      ·
                        rfl

theorem cell23_8008520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_8008520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008520 prefixEnd_8008520 := by exact prefixLift 8008520
  have htrace : WordTrace (prefixWord ++ tailWord_8008520) baseStart_8008520 baseEnd_8008520 := by
    simpa [prefixWord, tailWord_8008520, baseEnd_8008520] using wordTrace_append hprefix tailTrace_8008520
  have hstable : (prefixWord ++ tailWord_8008520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008520).length < 2 ^ (prefixWord ++ tailWord_8008520).sum := by decide
  have hdescent : baseEnd_8008520 < baseStart_8008520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008533 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_8008533 : Nat := 118140960795 + 8008533 * 2 ^ 59
def prefixEnd_8008533 : Nat := 4983230072969 + 3 ^ 40 * 8008533 * 2
def baseEnd_8008533 : Nat := 4112226766393620311506933

theorem tailTrace_8008533 : CollatzResearch.WordTrace tailWord_8008533 prefixEnd_8008533 4112226766393620311506933 := by
  unfold tailWord_8008533
  simp only [CollatzResearch.WordTrace]
  refine ⟨292095195095460164389486253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194730130063640109592990835 292095195095460164389486253)
  ·
    refine ⟨109535698160797561646057345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292095195095460164389486253 109535698160797561646057345)
    ·
      refine ⟨82151773620598171234543009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109535698160797561646057345 82151773620598171234543009)
      ·
        refine ⟨61613830215448628425907257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82151773620598171234543009 61613830215448628425907257)
        ·
          refine ⟨46210372661586471319430443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61613830215448628425907257 46210372661586471319430443)
          ·
            refine ⟨69315558992379706979145665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46210372661586471319430443 69315558992379706979145665)
            ·
              refine ⟨51986669244284780234359249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69315558992379706979145665 51986669244284780234359249)
              ·
                refine ⟨38990001933213585175769437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51986669244284780234359249 38990001933213585175769437)
                ·
                  refine ⟨14621250724955094440913539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38990001933213585175769437 14621250724955094440913539)
                  ·
                    refine ⟨21931876087432641661370309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14621250724955094440913539 21931876087432641661370309)
                    ·
                      refine ⟨4112226766393620311506933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21931876087432641661370309 4112226766393620311506933)
                      ·
                        rfl

theorem cell23_8008533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_8008533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008533 prefixEnd_8008533 := by exact prefixLift 8008533
  have htrace : WordTrace (prefixWord ++ tailWord_8008533) baseStart_8008533 baseEnd_8008533 := by
    simpa [prefixWord, tailWord_8008533, baseEnd_8008533] using wordTrace_append hprefix tailTrace_8008533
  have hstable : (prefixWord ++ tailWord_8008533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008533).length < 2 ^ (prefixWord ++ tailWord_8008533).sum := by decide
  have hdescent : baseEnd_8008533 < baseStart_8008533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008556 : List Nat := [2, 2, 1, 1, 4, 1, 1, 11]
def baseStart_8008556 : Nat := 118140960795 + 8008556 * 2 ^ 59
def prefixEnd_8008556 : Nat := 4983230072969 + 3 ^ 40 * 8008556 * 2
def baseEnd_8008556 : Nat := 152305132461061989685901

theorem tailTrace_8008556 : CollatzResearch.WordTrace tailWord_8008556 prefixEnd_8008556 152305132461061989685901 := by
  unfold tailWord_8008556
  simp only [CollatzResearch.WordTrace]
  refine ⟨146048016987188419658786761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194730689316251226211715681 146048016987188419658786761)
  ·
    refine ⟨109536012740391314744090071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146048016987188419658786761 109536012740391314744090071)
    ·
      refine ⟨164304019110586972116135107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109536012740391314744090071 164304019110586972116135107)
      ·
        refine ⟨246456028665880458174202661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164304019110586972116135107 246456028665880458174202661)
        ·
          refine ⟨46210505374852585907662999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246456028665880458174202661 46210505374852585907662999)
          ·
            refine ⟨69315758062278878861494499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46210505374852585907662999 69315758062278878861494499)
            ·
              refine ⟨103973637093418318292241749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69315758062278878861494499 103973637093418318292241749)
              ·
                refine ⟨152305132461061989685901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 103973637093418318292241749 152305132461061989685901)
                ·
                  rfl

theorem cell23_8008556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 11].length) (baseStart_8008556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008556 prefixEnd_8008556 := by exact prefixLift 8008556
  have htrace : WordTrace (prefixWord ++ tailWord_8008556) baseStart_8008556 baseEnd_8008556 := by
    simpa [prefixWord, tailWord_8008556, baseEnd_8008556] using wordTrace_append hprefix tailTrace_8008556
  have hstable : (prefixWord ++ tailWord_8008556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008556).length < 2 ^ (prefixWord ++ tailWord_8008556).sum := by decide
  have hdescent : baseEnd_8008556 < baseStart_8008556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008576 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_8008576 : Nat := 118140960795 + 8008576 * 2 ^ 59
def prefixEnd_8008576 : Nat := 4983230072969 + 3 ^ 40 * 8008576 * 2
def baseEnd_8008576 : Nat := 4112248846061763643269235

theorem tailTrace_8008576 : CollatzResearch.WordTrace tailWord_8008576 prefixEnd_8008576 4112248846061763643269235 := by
  unfold tailWord_8008576
  simp only [CollatzResearch.WordTrace]
  refine ⟨146048381717152191366650791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194731175622869588488867721 146048381717152191366650791)
  ·
    refine ⟨219072572575728287049976187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146048381717152191366650791 219072572575728287049976187)
    ·
      refine ⟨328608858863592430574964281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219072572575728287049976187 328608858863592430574964281)
      ·
        refine ⟨246456644147694322931223211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328608858863592430574964281 246456644147694322931223211)
        ·
          refine ⟨369684966221541484396834817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246456644147694322931223211 369684966221541484396834817)
          ·
            refine ⟨277263724666156113297626113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369684966221541484396834817 277263724666156113297626113)
            ·
              refine ⟨207947793499617084973219585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277263724666156113297626113 207947793499617084973219585)
              ·
                refine ⟨155960845124712813729914689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207947793499617084973219585 155960845124712813729914689)
                ·
                  refine ⟨116970633843534610297436017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155960845124712813729914689 116970633843534610297436017)
                  ·
                    refine ⟨87727975382650957723077013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116970633843534610297436017 87727975382650957723077013)
                    ·
                      refine ⟨4112248846061763643269235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87727975382650957723077013 4112248846061763643269235)
                      ·
                        rfl

theorem cell23_8008576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_8008576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008576 prefixEnd_8008576 := by exact prefixLift 8008576
  have htrace : WordTrace (prefixWord ++ tailWord_8008576) baseStart_8008576 baseEnd_8008576 := by
    simpa [prefixWord, tailWord_8008576, baseEnd_8008576] using wordTrace_append hprefix tailTrace_8008576
  have hstable : (prefixWord ++ tailWord_8008576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008576).length < 2 ^ (prefixWord ++ tailWord_8008576).sum := by decide
  have hdescent : baseEnd_8008576 < baseStart_8008576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008578 : List Nat := [3, 4, 2, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_8008578 : Nat := 118140960795 + 8008578 * 2 ^ 59
def prefixEnd_8008578 : Nat := 4983230072969 + 3 ^ 40 * 8008578 * 2
def baseEnd_8008578 : Nat := 4112249873023072635444227

theorem tailTrace_8008578 : CollatzResearch.WordTrace tailWord_8008578 prefixEnd_8008578 4112249873023072635444227 := by
  unfold tailWord_8008578
  simp only [CollatzResearch.WordTrace]
  refine ⟨73024209095074284268718597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194731224253531424716582925 73024209095074284268718597)
  ·
    refine ⟨13692039205326428300384737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73024209095074284268718597 13692039205326428300384737)
    ·
      refine ⟨10269029403994821225288553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13692039205326428300384737 10269029403994821225288553)
      ·
        refine ⟨7701772052996115918966415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10269029403994821225288553 7701772052996115918966415)
        ·
          refine ⟨11552658079494173878449623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701772052996115918966415 11552658079494173878449623)
          ·
            refine ⟨17328987119241260817674435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552658079494173878449623 17328987119241260817674435)
            ·
              refine ⟨25993480678861891226511653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17328987119241260817674435 25993480678861891226511653)
              ·
                refine ⟨4873777627286604604970935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25993480678861891226511653 4873777627286604604970935)
                ·
                  refine ⟨7310666440929906907456403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873777627286604604970935 7310666440929906907456403)
                  ·
                    refine ⟨10965999661394860361184605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7310666440929906907456403 10965999661394860361184605)
                    ·
                      refine ⟨4112249873023072635444227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10965999661394860361184605 4112249873023072635444227)
                      ·
                        rfl

theorem cell23_8008578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_8008578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008578 prefixEnd_8008578 := by exact prefixLift 8008578
  have htrace : WordTrace (prefixWord ++ tailWord_8008578) baseStart_8008578 baseEnd_8008578 := by
    simpa [prefixWord, tailWord_8008578, baseEnd_8008578] using wordTrace_append hprefix tailTrace_8008578
  have hstable : (prefixWord ++ tailWord_8008578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008578).length < 2 ^ (prefixWord ++ tailWord_8008578).sum := by decide
  have hdescent : baseEnd_8008578 < baseStart_8008578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008633 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 2, 6]
def baseStart_8008633 : Nat := 118140960795 + 8008633 * 2 ^ 59
def prefixEnd_8008633 : Nat := 4983230072969 + 3 ^ 40 * 8008633 * 2
def baseEnd_8008633 : Nat := 1370759371486356640085491

theorem tailTrace_8008633 : CollatzResearch.WordTrace tailWord_8008633 prefixEnd_8008633 1370759371486356640085491 := by
  unfold tailWord_8008633
  simp only [CollatzResearch.WordTrace]
  refine ⟨292098842395097881468126553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194732561596731920978751035 292098842395097881468126553)
  ·
    refine ⟨219074131796323411101094915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292098842395097881468126553 219074131796323411101094915)
    ·
      refine ⟨328611197694485116651642373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219074131796323411101094915 328611197694485116651642373)
      ·
        refine ⟨61614599567715959372182945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328611197694485116651642373 61614599567715959372182945)
        ·
          refine ⟨46210949675786969529137209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61614599567715959372182945 46210949675786969529137209)
          ·
            refine ⟨34658212256840227146852907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46210949675786969529137209 34658212256840227146852907)
            ·
              refine ⟨51987318385260340720279361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34658212256840227146852907 51987318385260340720279361)
              ·
                refine ⟨38990488788945255540209521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51987318385260340720279361 38990488788945255540209521)
                ·
                  refine ⟨29242866591708941655157141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38990488788945255540209521 29242866591708941655157141)
                  ·
                    refine ⟨1370759371486356640085491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29242866591708941655157141 1370759371486356640085491)
                    ·
                      rfl

theorem cell23_8008633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_8008633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008633 prefixEnd_8008633 := by exact prefixLift 8008633
  have htrace : WordTrace (prefixWord ++ tailWord_8008633) baseStart_8008633 baseEnd_8008633 := by
    simpa [prefixWord, tailWord_8008633, baseEnd_8008633] using wordTrace_append hprefix tailTrace_8008633
  have hstable : (prefixWord ++ tailWord_8008633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008633).length < 2 ^ (prefixWord ++ tailWord_8008633).sum := by decide
  have hdescent : baseEnd_8008633 < baseStart_8008633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008677 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_8008677 : Nat := 118140960795 + 8008677 * 2 ^ 59
def prefixEnd_8008677 : Nat := 4983230072969 + 3 ^ 40 * 8008677 * 2
def baseEnd_8008677 : Nat := 4112300707607867748106271

theorem tailTrace_8008677 : CollatzResearch.WordTrace tailWord_8008677 prefixEnd_8008677 4112300707607867748106271 := by
  unfold tailWord_8008677
  simp only [CollatzResearch.WordTrace]
  refine ⟨292100447206938476982728285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194733631471292317988485523 292100447206938476982728285)
  ·
    refine ⟨109537667702601928868523107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292100447206938476982728285 109537667702601928868523107)
    ·
      refine ⟨164306501553902893302784661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109537667702601928868523107 164306501553902893302784661)
      ·
        refine ⟨7701867260339198123568031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164306501553902893302784661 7701867260339198123568031)
        ·
          refine ⟨11552800890508797185352047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701867260339198123568031 11552800890508797185352047)
          ·
            refine ⟨17329201335763195778028071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552800890508797185352047 17329201335763195778028071)
            ·
              refine ⟨25993802003644793667042107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17329201335763195778028071 25993802003644793667042107)
              ·
                refine ⟨38990703005467190500563161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25993802003644793667042107 38990703005467190500563161)
                ·
                  refine ⟨29243027254100392875422371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38990703005467190500563161 29243027254100392875422371)
                  ·
                    refine ⟨43864540881150589313133557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29243027254100392875422371 43864540881150589313133557)
                    ·
                      refine ⟨4112300707607867748106271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43864540881150589313133557 4112300707607867748106271)
                      ·
                        rfl

theorem cell23_8008677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_8008677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008677 prefixEnd_8008677 := by exact prefixLift 8008677
  have htrace : WordTrace (prefixWord ++ tailWord_8008677) baseStart_8008677 baseEnd_8008677 := by
    simpa [prefixWord, tailWord_8008677, baseEnd_8008677] using wordTrace_append hprefix tailTrace_8008677
  have hstable : (prefixWord ++ tailWord_8008677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008677).length < 2 ^ (prefixWord ++ tailWord_8008677).sum := by decide
  have hdescent : baseEnd_8008677 < baseStart_8008677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008697 : List Nat := [1, 2, 1, 3, 1, 3, 5, 2, 5]
def baseStart_8008697 : Nat := 118140960795 + 8008697 * 2 ^ 59
def prefixEnd_8008697 : Nat := 4983230072969 + 3 ^ 40 * 8008697 * 2
def baseEnd_8008697 : Nat := 456923441913439741095131

theorem tailTrace_8008697 : CollatzResearch.WordTrace tailWord_8008697 prefixEnd_8008697 456923441913439741095131 := by
  unfold tailWord_8008697
  simp only [CollatzResearch.WordTrace]
  refine ⟨292101176666866020398456345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194734117777910680265637563 292101176666866020398456345)
  ·
    refine ⟨219075882500149515298842259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292101176666866020398456345 219075882500149515298842259)
    ·
      refine ⟨328613823750224272948263389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219075882500149515298842259 328613823750224272948263389)
      ·
        refine ⟨123230183906334102355598771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328613823750224272948263389 123230183906334102355598771)
        ·
          refine ⟨184845275859501153533398157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123230183906334102355598771 184845275859501153533398157)
          ·
            refine ⟨69316978447312932575024309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184845275859501153533398157 69316978447312932575024309)
            ·
              refine ⟨6498466729435587428908529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69316978447312932575024309 6498466729435587428908529)
              ·
                refine ⟨4873850047076690571681397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498466729435587428908529 4873850047076690571681397)
                ·
                  refine ⟨456923441913439741095131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4873850047076690571681397 456923441913439741095131)
                  ·
                    rfl

theorem cell23_8008697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 5].length) (baseStart_8008697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008697 prefixEnd_8008697 := by exact prefixLift 8008697
  have htrace : WordTrace (prefixWord ++ tailWord_8008697) baseStart_8008697 baseEnd_8008697 := by
    simpa [prefixWord, tailWord_8008697, baseEnd_8008697] using wordTrace_append hprefix tailTrace_8008697
  have hstable : (prefixWord ++ tailWord_8008697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008697).length < 2 ^ (prefixWord ++ tailWord_8008697).sum := by decide
  have hdescent : baseEnd_8008697 < baseStart_8008697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008713 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_8008713 : Nat := 118140960795 + 8008713 * 2 ^ 59
def prefixEnd_8008713 : Nat := 4983230072969 + 3 ^ 40 * 8008713 * 2
def baseEnd_8008713 : Nat := 4112319192911429607256105

theorem tailTrace_8008713 : CollatzResearch.WordTrace tailWord_8008713 prefixEnd_8008713 4112319192911429607256105 := by
  unfold tailWord_8008713
  simp only [CollatzResearch.WordTrace]
  refine ⟨292101760234808055131038793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194734506823205370087359195 292101760234808055131038793)
  ·
    refine ⟨219076320176106041348279095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292101760234808055131038793 219076320176106041348279095)
    ·
      refine ⟨328614480264159062022418643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219076320176106041348279095 328614480264159062022418643)
      ·
        refine ⟨492921720396238593033627965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328614480264159062022418643 492921720396238593033627965)
        ·
          refine ⟨184845645148589472387610487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492921720396238593033627965 184845645148589472387610487)
          ·
            refine ⟨277268467722884208581415731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184845645148589472387610487 277268467722884208581415731)
            ·
              refine ⟨415902701584326312872123597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277268467722884208581415731 415902701584326312872123597)
              ·
                refine ⟨155963513094122367327046349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415902701584326312872123597 155963513094122367327046349)
                ·
                  refine ⟨58486317410295887747642381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155963513094122367327046349 58486317410295887747642381)
                  ·
                    refine ⟨21932369028860957905365893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58486317410295887747642381 21932369028860957905365893)
                    ·
                      refine ⟨4112319192911429607256105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21932369028860957905365893 4112319192911429607256105)
                      ·
                        rfl

theorem cell23_8008713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_8008713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008713 prefixEnd_8008713 := by exact prefixLift 8008713
  have htrace : WordTrace (prefixWord ++ tailWord_8008713) baseStart_8008713 baseEnd_8008713 := by
    simpa [prefixWord, tailWord_8008713, baseEnd_8008713] using wordTrace_append hprefix tailTrace_8008713
  have hstable : (prefixWord ++ tailWord_8008713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008713).length < 2 ^ (prefixWord ++ tailWord_8008713).sum := by decide
  have hdescent : baseEnd_8008713 < baseStart_8008713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008727 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 2, 5]
def baseStart_8008727 : Nat := 118140960795 + 8008727 * 2 ^ 59
def prefixEnd_8008727 : Nat := 4983230072969 + 3 ^ 40 * 8008727 * 2
def baseEnd_8008727 : Nat := 1370775460546864184160347

theorem tailTrace_8008727 : CollatzResearch.WordTrace tailWord_8008727 prefixEnd_8008727 1370775460546864184160347 := by
  unfold tailWord_8008727
  simp only [CollatzResearch.WordTrace]
  refine ⟨292102270856757335522048435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194734847237838223681365623 292102270856757335522048435)
  ·
    refine ⟨438153406285136003283072653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292102270856757335522048435 438153406285136003283072653)
    ·
      refine ⟨164307527356926001231152245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438153406285136003283072653 164307527356926001231152245)
      ·
        refine ⟨15403830689711812615420523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164307527356926001231152245 15403830689711812615420523)
        ·
          refine ⟨23105746034567718923130785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15403830689711812615420523 23105746034567718923130785)
          ·
            refine ⟨17329309525925789192348089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23105746034567718923130785 17329309525925789192348089)
            ·
              refine ⟨12996982144444341894261067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17329309525925789192348089 12996982144444341894261067)
              ·
                refine ⟨19495473216666512841391601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12996982144444341894261067 19495473216666512841391601)
                ·
                  refine ⟨14621604912499884631043701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19495473216666512841391601 14621604912499884631043701)
                  ·
                    refine ⟨1370775460546864184160347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14621604912499884631043701 1370775460546864184160347)
                    ·
                      rfl

theorem cell23_8008727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_8008727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008727 prefixEnd_8008727 := by exact prefixLift 8008727
  have htrace : WordTrace (prefixWord ++ tailWord_8008727) baseStart_8008727 baseEnd_8008727 := by
    simpa [prefixWord, tailWord_8008727, baseEnd_8008727] using wordTrace_append hprefix tailTrace_8008727
  have hstable : (prefixWord ++ tailWord_8008727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008727).length < 2 ^ (prefixWord ++ tailWord_8008727).sum := by decide
  have hdescent : baseEnd_8008727 < baseStart_8008727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008750 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_8008750 : Nat := 118140960795 + 8008750 * 2 ^ 59
def prefixEnd_8008750 : Nat := 4983230072969 + 3 ^ 40 * 8008750 * 2
def baseEnd_8008750 : Nat := 4112338191695645962493435

theorem tailTrace_8008750 : CollatzResearch.WordTrace tailWord_8008750 prefixEnd_8008750 4112338191695645962493435 := by
  unfold tailWord_8008750
  simp only [CollatzResearch.WordTrace]
  refine ⟨36512888716959251306266963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194735406490449340300090469 36512888716959251306266963)
  ·
    refine ⟨54769333075438876959400445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36512888716959251306266963 54769333075438876959400445)
    ·
      refine ⟨20538499903289578859775167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54769333075438876959400445 20538499903289578859775167)
      ·
        refine ⟨30807749854934368289662751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20538499903289578859775167 30807749854934368289662751)
        ·
          refine ⟨46211624782401552434494127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30807749854934368289662751 46211624782401552434494127)
          ·
            refine ⟨69317437173602328651741191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46211624782401552434494127 69317437173602328651741191)
            ·
              refine ⟨103976155760403492977611787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69317437173602328651741191 103976155760403492977611787)
              ·
                refine ⟨155964233640605239466417681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103976155760403492977611787 155964233640605239466417681)
                ·
                  refine ⟨116973175230453929599813261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155964233640605239466417681 116973175230453929599813261)
                  ·
                    refine ⟨43864940711420223599929973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116973175230453929599813261 43864940711420223599929973)
                    ·
                      refine ⟨4112338191695645962493435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43864940711420223599929973 4112338191695645962493435)
                      ·
                        rfl

theorem cell23_8008750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_8008750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008750 prefixEnd_8008750 := by exact prefixLift 8008750
  have htrace : WordTrace (prefixWord ++ tailWord_8008750) baseStart_8008750 baseEnd_8008750 := by
    simpa [prefixWord, tailWord_8008750, baseEnd_8008750] using wordTrace_append hprefix tailTrace_8008750
  have hstable : (prefixWord ++ tailWord_8008750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008750).length < 2 ^ (prefixWord ++ tailWord_8008750).sum := by decide
  have hdescent : baseEnd_8008750 < baseStart_8008750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008774 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_8008774 : Nat := 118140960795 + 8008774 * 2 ^ 59
def prefixEnd_8008774 : Nat := 4983230072969 + 3 ^ 40 * 8008774 * 2
def baseEnd_8008774 : Nat := 1370783505077117956197775

theorem tailTrace_8008774 : CollatzResearch.WordTrace tailWord_8008774 prefixEnd_8008774 1370783505077117956197775 := by
  unfold tailWord_8008774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9128249533987095704656543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194735990058391375032672917 9128249533987095704656543)
  ·
    refine ⟨13692374300980643556984815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9128249533987095704656543 13692374300980643556984815)
    ·
      refine ⟨20538561451470965335477223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13692374300980643556984815 20538561451470965335477223)
      ·
        refine ⟨30807842177206448003215835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20538561451470965335477223 30807842177206448003215835)
        ·
          refine ⟨46211763265809672004823753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30807842177206448003215835 46211763265809672004823753)
          ·
            refine ⟨34658822449357254003617815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46211763265809672004823753 34658822449357254003617815)
            ·
              refine ⟨51988233674035881005426723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34658822449357254003617815 51988233674035881005426723)
              ·
                refine ⟨77982350511053821508140085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51988233674035881005426723 77982350511053821508140085)
                ·
                  refine ⟨7310845360411295766388133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77982350511053821508140085 7310845360411295766388133)
                  ·
                    refine ⟨1370783505077117956197775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7310845360411295766388133 1370783505077117956197775)
                    ·
                      rfl

theorem cell23_8008774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_8008774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008774 prefixEnd_8008774 := by exact prefixLift 8008774
  have htrace : WordTrace (prefixWord ++ tailWord_8008774) baseStart_8008774 baseEnd_8008774 := by
    simpa [prefixWord, tailWord_8008774, baseEnd_8008774] using wordTrace_append hprefix tailTrace_8008774
  have hstable : (prefixWord ++ tailWord_8008774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008774).length < 2 ^ (prefixWord ++ tailWord_8008774).sum := by decide
  have hdescent : baseEnd_8008774 < baseStart_8008774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008814 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_8008814 : Nat := 118140960795 + 8008814 * 2 ^ 59
def prefixEnd_8008814 : Nat := 4983230072969 + 3 ^ 40 * 8008814 * 2
def baseEnd_8008814 : Nat := 4112371054457533712093141

theorem tailTrace_8008814 : CollatzResearch.WordTrace tailWord_8008814 prefixEnd_8008814 4112371054457533712093141 := by
  unfold tailWord_8008814
  simp only [CollatzResearch.WordTrace]
  refine ⟨36513180500930268672558187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194736962671628099586976997 36513180500930268672558187)
  ·
    refine ⟨54769770751395403008837281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36513180500930268672558187 54769770751395403008837281)
    ·
      refine ⟨41077328063546552256627961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54769770751395403008837281 41077328063546552256627961)
      ·
        refine ⟨30807996047659914192470971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41077328063546552256627961 30807996047659914192470971)
        ·
          refine ⟨46211994071489871288706457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30807996047659914192470971 46211994071489871288706457)
          ·
            refine ⟨34658995553617403466529843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46211994071489871288706457 34658995553617403466529843)
            ·
              refine ⟨51988493330426105199794765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34658995553617403466529843 51988493330426105199794765)
              ·
                refine ⟨19495684998909789449923037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51988493330426105199794765 19495684998909789449923037)
                ·
                  refine ⟨7310881874591171043721139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19495684998909789449923037 7310881874591171043721139)
                  ·
                    refine ⟨10966322811886756565581709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7310881874591171043721139 10966322811886756565581709)
                    ·
                      refine ⟨4112371054457533712093141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10966322811886756565581709 4112371054457533712093141)
                      ·
                        rfl

theorem cell23_8008814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_8008814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008814 prefixEnd_8008814 := by exact prefixLift 8008814
  have htrace : WordTrace (prefixWord ++ tailWord_8008814) baseStart_8008814 baseEnd_8008814 := by
    simpa [prefixWord, tailWord_8008814, baseEnd_8008814] using wordTrace_append hprefix tailTrace_8008814
  have hstable : (prefixWord ++ tailWord_8008814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008814).length < 2 ^ (prefixWord ++ tailWord_8008814).sum := by decide
  have hdescent : baseEnd_8008814 < baseStart_8008814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008821 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 6]
def baseStart_8008821 : Nat := 118140960795 + 8008821 * 2 ^ 59
def prefixEnd_8008821 : Nat := 4983230072969 + 3 ^ 40 * 8008821 * 2
def baseEnd_8008821 : Nat := 456930516535790576078401

theorem tailTrace_8008821 : CollatzResearch.WordTrace tailWord_8008821 prefixEnd_8008821 456930516535790576078401 := by
  unfold tailWord_8008821
  simp only [CollatzResearch.WordTrace]
  refine ⟨292105699318416789575970317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194737132878944526383980211 292105699318416789575970317)
  ·
    refine ⟨109539637244406296090988869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292105699318416789575970317 109539637244406296090988869)
    ·
      refine ⟨20538681983326180517060413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109539637244406296090988869 20538681983326180517060413)
      ·
        refine ⟨7702005743747317693897655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20538681983326180517060413 7702005743747317693897655)
        ·
          refine ⟨11553008615620976540846483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7702005743747317693897655 11553008615620976540846483)
          ·
            refine ⟨17329512923431464811269725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11553008615620976540846483 17329512923431464811269725)
            ·
              refine ⟨6498567346286799304226147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17329512923431464811269725 6498567346286799304226147)
              ·
                refine ⟨9747851019430198956339221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498567346286799304226147 9747851019430198956339221)
                ·
                  refine ⟨456930516535790576078401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9747851019430198956339221 456930516535790576078401)
                  ·
                    rfl

theorem cell23_8008821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_8008821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008821 prefixEnd_8008821 := by exact prefixLift 8008821
  have htrace : WordTrace (prefixWord ++ tailWord_8008821) baseStart_8008821 baseEnd_8008821 := by
    simpa [prefixWord, tailWord_8008821, baseEnd_8008821] using wordTrace_append hprefix tailTrace_8008821
  have hstable : (prefixWord ++ tailWord_8008821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008821).length < 2 ^ (prefixWord ++ tailWord_8008821).sum := by decide
  have hdescent : baseEnd_8008821 < baseStart_8008821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008860 : List Nat := [2, 2, 3, 2, 1, 2, 11]
def baseStart_8008860 : Nat := 118140960795 + 8008860 * 2 ^ 59
def prefixEnd_8008860 : Nat := 4983230072969 + 3 ^ 40 * 8008860 * 2
def baseEnd_8008860 : Nat := 50770304624291858421209

theorem tailTrace_8008860 : CollatzResearch.WordTrace tailWord_8008860 prefixEnd_8008860 50770304624291858421209 := by
  unfold tailWord_8008860
  simp only [CollatzResearch.WordTrace]
  refine ⟨146053560882637749618320017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194738081176850332824426689 146053560882637749618320017)
  ·
    refine ⟨109540170661978312213740013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146053560882637749618320017 109540170661978312213740013)
    ·
      refine ⟨41077563998241867080152505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109540170661978312213740013 41077563998241867080152505)
      ·
        refine ⟨30808172998681400310114379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41077563998241867080152505 30808172998681400310114379)
        ·
          refine ⟨46212259498022100465171569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30808172998681400310114379 46212259498022100465171569)
          ·
            refine ⟨34659194623516575348878677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46212259498022100465171569 34659194623516575348878677)
            ·
              refine ⟨50770304624291858421209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34659194623516575348878677 50770304624291858421209)
              ·
                rfl

theorem cell23_8008860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 11].length) (baseStart_8008860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008860 prefixEnd_8008860 := by exact prefixLift 8008860
  have htrace : WordTrace (prefixWord ++ tailWord_8008860) baseStart_8008860 baseEnd_8008860 := by
    simpa [prefixWord, tailWord_8008860, baseEnd_8008860] using wordTrace_append hprefix tailTrace_8008860
  have hstable : (prefixWord ++ tailWord_8008860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008860).length < 2 ^ (prefixWord ++ tailWord_8008860).sum := by decide
  have hdescent : baseEnd_8008860 < baseStart_8008860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008874 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_8008874 : Nat := 118140960795 + 8008874 * 2 ^ 59
def prefixEnd_8008874 : Nat := 4983230072969 + 3 ^ 40 * 8008874 * 2
def baseEnd_8008874 : Nat := 4112401863296803477342865

theorem tailTrace_8008874 : CollatzResearch.WordTrace tailWord_8008874 prefixEnd_8008874 4112401863296803477342865 := by
  unfold tailWord_8008874
  simp only [CollatzResearch.WordTrace]
  refine ⟨73026908096806194906912419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194738421591483186418433117 73026908096806194906912419)
  ·
    refine ⟨109540362145209292360368629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73026908096806194906912419 109540362145209292360368629)
    ·
      refine ⟨10269408951113371158784559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109540362145209292360368629 10269408951113371158784559)
      ·
        refine ⟨15404113426670056738176839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10269408951113371158784559 15404113426670056738176839)
        ·
          refine ⟨23106170140005085107265259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15404113426670056738176839 23106170140005085107265259)
          ·
            refine ⟨34659255210007627660897889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23106170140005085107265259 34659255210007627660897889)
            ·
              refine ⟨25994441407505720745673417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34659255210007627660897889 25994441407505720745673417)
              ·
                refine ⟨19495831055629290559255063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25994441407505720745673417 19495831055629290559255063)
                ·
                  refine ⟨29243746583443935838882595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19495831055629290559255063 29243746583443935838882595)
                  ·
                    refine ⟨43865619875165903758323893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29243746583443935838882595 43865619875165903758323893)
                    ·
                      refine ⟨4112401863296803477342865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43865619875165903758323893 4112401863296803477342865)
                      ·
                        rfl

theorem cell23_8008874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_8008874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008874 prefixEnd_8008874 := by exact prefixLift 8008874
  have htrace : WordTrace (prefixWord ++ tailWord_8008874) baseStart_8008874 baseEnd_8008874 := by
    simpa [prefixWord, tailWord_8008874, baseEnd_8008874] using wordTrace_append hprefix tailTrace_8008874
  have hstable : (prefixWord ++ tailWord_8008874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008874).length < 2 ^ (prefixWord ++ tailWord_8008874).sum := by decide
  have hdescent : baseEnd_8008874 < baseStart_8008874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008881 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 2, 4]
def baseStart_8008881 : Nat := 118140960795 + 8008881 * 2 ^ 59
def prefixEnd_8008881 : Nat := 4983230072969 + 3 ^ 40 * 8008881 * 2
def baseEnd_8008881 : Nat := 1370801819220461649985111

theorem tailTrace_8008881 : CollatzResearch.WordTrace tailWord_8008881 prefixEnd_8008881 1370801819220461649985111 := by
  unfold tailWord_8008881
  simp only [CollatzResearch.WordTrace]
  refine ⟨292107887698199419823154497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194738591798799613215436331 292107887698199419823154497)
  ·
    refine ⟨219080915773649564867365873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292107887698199419823154497 219080915773649564867365873)
    ·
      refine ⟨164310686830237173650524405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219080915773649564867365873 164310686830237173650524405)
      ·
        refine ⟨15404126890334735029736663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164310686830237173650524405 15404126890334735029736663)
        ·
          refine ⟨23106190335502102544604995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15404126890334735029736663 23106190335502102544604995)
          ·
            refine ⟨34659285503253153816907493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23106190335502102544604995 34659285503253153816907493)
            ·
              refine ⟨6498616031859966340670155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34659285503253153816907493 6498616031859966340670155)
              ·
                refine ⟨9747924047789949511005233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498616031859966340670155 9747924047789949511005233)
                ·
                  refine ⟨7310943035842462133253925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9747924047789949511005233 7310943035842462133253925)
                  ·
                    refine ⟨1370801819220461649985111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7310943035842462133253925 1370801819220461649985111)
                    ·
                      rfl

theorem cell23_8008881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_8008881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008881 prefixEnd_8008881 := by exact prefixLift 8008881
  have htrace : WordTrace (prefixWord ++ tailWord_8008881) baseStart_8008881 baseEnd_8008881 := by
    simpa [prefixWord, tailWord_8008881, baseEnd_8008881] using wordTrace_append hprefix tailTrace_8008881
  have hstable : (prefixWord ++ tailWord_8008881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008881).length < 2 ^ (prefixWord ++ tailWord_8008881).sum := by decide
  have hdescent : baseEnd_8008881 < baseStart_8008881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008887 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_8008887 : Nat := 118140960795 + 8008887 * 2 ^ 59
def prefixEnd_8008887 : Nat := 4983230072969 + 3 ^ 40 * 8008887 * 2
def baseEnd_8008887 : Nat := 4112408538545311926480305

theorem tailTrace_8008887 : CollatzResearch.WordTrace tailWord_8008887 prefixEnd_8008887 4112408538545311926480305 := by
  unfold tailWord_8008887
  simp only [CollatzResearch.WordTrace]
  refine ⟨292108106536177682847872915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194738737690785121898581943 292108106536177682847872915)
  ·
    refine ⟨438162159804266524271809373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292108106536177682847872915 438162159804266524271809373)
    ·
      refine ⟨164310809926599946601928515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438162159804266524271809373 164310809926599946601928515)
      ·
        refine ⟨246466214889899919902892773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164310809926599946601928515 246466214889899919902892773)
        ·
          refine ⟨46212415291856234981792395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246466214889899919902892773 46212415291856234981792395)
          ·
            refine ⟨69318622937784352472688593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46212415291856234981792395 69318622937784352472688593)
            ·
              refine ⟨51988967203338264354516445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69318622937784352472688593 51988967203338264354516445)
              ·
                refine ⟨19495862701251849132943667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51988967203338264354516445 19495862701251849132943667)
                ·
                  refine ⟨29243794051877773699415501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19495862701251849132943667 29243794051877773699415501)
                  ·
                    refine ⟨10966422769454165137280813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29243794051877773699415501 10966422769454165137280813)
                    ·
                      refine ⟨4112408538545311926480305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10966422769454165137280813 4112408538545311926480305)
                      ·
                        rfl

theorem cell23_8008887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_8008887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008887 prefixEnd_8008887 := by exact prefixLift 8008887
  have htrace : WordTrace (prefixWord ++ tailWord_8008887) baseStart_8008887 baseEnd_8008887 := by
    simpa [prefixWord, tailWord_8008887, baseEnd_8008887] using wordTrace_append hprefix tailTrace_8008887
  have hstable : (prefixWord ++ tailWord_8008887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008887).length < 2 ^ (prefixWord ++ tailWord_8008887).sum := by decide
  have hdescent : baseEnd_8008887 < baseStart_8008887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008944 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 8, 2, 2]
def baseStart_8008944 : Nat := 118140960795 + 8008944 * 2 ^ 59
def prefixEnd_8008944 : Nat := 4983230072969 + 3 ^ 40 * 8008944 * 2
def baseEnd_8008944 : Nat := 4112437806942618203467543

theorem tailTrace_8008944 : CollatzResearch.WordTrace tailWord_8008944 prefixEnd_8008944 4112437806942618203467543 := by
  unfold tailWord_8008944
  simp only [CollatzResearch.WordTrace]
  refine ⟨146055092748485590791348943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194740123664647454388465257 146055092748485590791348943)
  ·
    refine ⟨219082639122728386187023415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146055092748485590791348943 219082639122728386187023415)
    ·
      refine ⟨328623958684092579280535123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219082639122728386187023415 328623958684092579280535123)
      ·
        refine ⟨492935938026138868920802685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328623958684092579280535123 492935938026138868920802685)
        ·
          refine ⟨184850976759802075845301007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492935938026138868920802685 184850976759802075845301007)
          ·
            refine ⟨277276465139703113767951511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184850976759802075845301007 277276465139703113767951511)
            ·
              refine ⟨415914697709554670651927267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277276465139703113767951511 415914697709554670651927267)
              ·
                refine ⟨623872046564332005977890901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415914697709554670651927267 623872046564332005977890901)
                ·
                  refine ⟨7311000545675765695053409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 623872046564332005977890901 7311000545675765695053409)
                  ·
                    refine ⟨5483250409256824271290057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7311000545675765695053409 5483250409256824271290057)
                    ·
                      refine ⟨4112437806942618203467543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483250409256824271290057 4112437806942618203467543)
                      ·
                        rfl

theorem cell23_8008944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 2, 2].length) (baseStart_8008944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008944 prefixEnd_8008944 := by exact prefixLift 8008944
  have htrace : WordTrace (prefixWord ++ tailWord_8008944) baseStart_8008944 baseEnd_8008944 := by
    simpa [prefixWord, tailWord_8008944, baseEnd_8008944] using wordTrace_append hprefix tailTrace_8008944
  have hstable : (prefixWord ++ tailWord_8008944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008944).length < 2 ^ (prefixWord ++ tailWord_8008944).sum := by decide
  have hdescent : baseEnd_8008944 < baseStart_8008944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008960 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 7]
def baseStart_8008960 : Nat := 118140960795 + 8008960 * 2 ^ 59
def prefixEnd_8008960 : Nat := 4983230072969 + 3 ^ 40 * 8008960 * 2
def baseEnd_8008960 : Nat := 4112446022633090140867469

theorem tailTrace_8008960 : CollatzResearch.WordTrace tailWord_8008960 prefixEnd_8008960 4112446022633090140867469 := by
  unfold tailWord_8008960
  simp only [CollatzResearch.WordTrace]
  refine ⟨146055384532456608157640167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194740512709942144210186889 146055384532456608157640167)
  ·
    refine ⟨219083076798684912236460251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146055384532456608157640167 219083076798684912236460251)
    ·
      refine ⟨328624615198027368354690377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219083076798684912236460251 328624615198027368354690377)
      ·
        refine ⟨246468461398520526266017783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328624615198027368354690377 246468461398520526266017783)
        ·
          refine ⟨369702692097780789399026675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246468461398520526266017783 369702692097780789399026675)
          ·
            refine ⟨554554038146671184098540013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369702692097780789399026675 554554038146671184098540013)
            ·
              refine ⟨207957764305001694036952505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554554038146671184098540013 207957764305001694036952505)
              ·
                refine ⟨155968323228751270527714379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207957764305001694036952505 155968323228751270527714379)
                ·
                  refine ⟨233952484843126905791571569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155968323228751270527714379 233952484843126905791571569)
                  ·
                    refine ⟨175464363632345179343678677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233952484843126905791571569 175464363632345179343678677)
                    ·
                      refine ⟨4112446022633090140867469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175464363632345179343678677 4112446022633090140867469)
                      ·
                        rfl

theorem cell23_8008960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_8008960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008960 prefixEnd_8008960 := by exact prefixLift 8008960
  have htrace : WordTrace (prefixWord ++ tailWord_8008960) baseStart_8008960 baseEnd_8008960 := by
    simpa [prefixWord, tailWord_8008960, baseEnd_8008960] using wordTrace_append hprefix tailTrace_8008960
  have hstable : (prefixWord ++ tailWord_8008960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008960).length < 2 ^ (prefixWord ++ tailWord_8008960).sum := by decide
  have hdescent : baseEnd_8008960 < baseStart_8008960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008977 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_8008977 : Nat := 118140960795 + 8008977 * 2 ^ 59
def prefixEnd_8008977 : Nat := 4983230072969 + 3 ^ 40 * 8008977 * 2
def baseEnd_8008977 : Nat := 4112454751804216574354891

theorem tailTrace_8008977 : CollatzResearch.WordTrace tailWord_8008977 prefixEnd_8008977 4112454751804216574354891 := by
  unfold tailWord_8008977
  simp only [CollatzResearch.WordTrace]
  refine ⟨292111389105851628218649185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194740926070567752145766123 292111389105851628218649185)
  ·
    refine ⟨219083541829388721163986889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292111389105851628218649185 219083541829388721163986889)
    ·
      refine ⟨164312656372041540872990167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219083541829388721163986889 164312656372041540872990167)
      ·
        refine ⟨246468984558062311309485251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164312656372041540872990167 246468984558062311309485251)
        ·
          refine ⟨369703476837093466964227877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246468984558062311309485251 369703476837093466964227877)
          ·
            refine ⟨69319401906955025055792727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369703476837093466964227877 69319401906955025055792727)
            ·
              refine ⟨103979102860432537583689091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69319401906955025055792727 103979102860432537583689091)
              ·
                refine ⟨155968654290648806375533637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103979102860432537583689091 155968654290648806375533637)
                ·
                  refine ⟨29244122679496651195412557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155968654290648806375533637 29244122679496651195412557)
                  ·
                    refine ⟨10966546004811244198279709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29244122679496651195412557 10966546004811244198279709)
                    ·
                      refine ⟨4112454751804216574354891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10966546004811244198279709 4112454751804216574354891)
                      ·
                        rfl

theorem cell23_8008977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_8008977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008977 prefixEnd_8008977 := by exact prefixLift 8008977
  have htrace : WordTrace (prefixWord ++ tailWord_8008977) baseStart_8008977 baseEnd_8008977 := by
    simpa [prefixWord, tailWord_8008977, baseEnd_8008977] using wordTrace_append hprefix tailTrace_8008977
  have hstable : (prefixWord ++ tailWord_8008977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008977).length < 2 ^ (prefixWord ++ tailWord_8008977).sum := by decide
  have hdescent : baseEnd_8008977 < baseStart_8008977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008984 : List Nat := [2, 1, 2, 3, 1, 3, 2, 4, 5]
def baseStart_8008984 : Nat := 118140960795 + 8008984 * 2 ^ 59
def prefixEnd_8008984 : Nat := 4983230072969 + 3 ^ 40 * 8008984 * 2
def baseEnd_8008984 : Nat := 456939816240977560774151

theorem tailTrace_8008984 : CollatzResearch.WordTrace tailWord_8008984 prefixEnd_8008984 456939816240977560774151 := by
  unfold tailWord_8008984
  simp only [CollatzResearch.WordTrace]
  refine ⟨146055822208413134207077003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194741096277884178942769337 146055822208413134207077003)
  ·
    refine ⟨219083733312619701310615505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146055822208413134207077003 219083733312619701310615505)
    ·
      refine ⟨164312799984464775982961629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219083733312619701310615505 164312799984464775982961629)
      ·
        refine ⟨61617299994174290993610611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164312799984464775982961629 61617299994174290993610611)
        ·
          refine ⟨92425949991261436490415917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61617299994174290993610611 92425949991261436490415917)
          ·
            refine ⟨34659731246723038683905969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92425949991261436490415917 34659731246723038683905969)
            ·
              refine ⟨25994798435042279012929477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34659731246723038683905969 25994798435042279012929477)
              ·
                refine ⟨4874024706570427314924277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25994798435042279012929477 4874024706570427314924277)
                ·
                  refine ⟨456939816240977560774151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4874024706570427314924277 456939816240977560774151)
                  ·
                    rfl

theorem cell23_8008984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 5].length) (baseStart_8008984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008984 prefixEnd_8008984 := by exact prefixLift 8008984
  have htrace : WordTrace (prefixWord ++ tailWord_8008984) baseStart_8008984 baseEnd_8008984 := by
    simpa [prefixWord, tailWord_8008984, baseEnd_8008984] using wordTrace_append hprefix tailTrace_8008984
  have hstable : (prefixWord ++ tailWord_8008984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008984).length < 2 ^ (prefixWord ++ tailWord_8008984).sum := by decide
  have hdescent : baseEnd_8008984 < baseStart_8008984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8008997 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_8008997 : Nat := 118140960795 + 8008997 * 2 ^ 59
def prefixEnd_8008997 : Nat := 4983230072969 + 3 ^ 40 * 8008997 * 2
def baseEnd_8008997 : Nat := 1370821673805768832034933

theorem tailTrace_8008997 : CollatzResearch.WordTrace tailWord_8008997 prefixEnd_8008997 1370821673805768832034933 := by
  unfold tailWord_8008997
  simp only [CollatzResearch.WordTrace]
  refine ⟨292112118565779171634377245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194741412377186114422918163 292112118565779171634377245)
  ·
    refine ⟨109542044462167189362891467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292112118565779171634377245 109542044462167189362891467)
    ·
      refine ⟨164313066693250784044337201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109542044462167189362891467 164313066693250784044337201)
      ·
        refine ⟨123234800019938088033252901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164313066693250784044337201 123234800019938088033252901)
        ·
          refine ⟨23106525003738391506234919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123234800019938088033252901 23106525003738391506234919)
          ·
            refine ⟨34659787505607587259352379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23106525003738391506234919 34659787505607587259352379)
            ·
              refine ⟨51989681258411380889028569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34659787505607587259352379 51989681258411380889028569)
              ·
                refine ⟨38992260943808535666771427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51989681258411380889028569 38992260943808535666771427)
                ·
                  refine ⟨58488391415712803500157141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38992260943808535666771427 58488391415712803500157141)
                  ·
                    refine ⟨1370821673805768832034933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58488391415712803500157141 1370821673805768832034933)
                    ·
                      rfl

theorem cell23_8008997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_8008997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8008997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8008997 prefixEnd_8008997 := by exact prefixLift 8008997
  have htrace : WordTrace (prefixWord ++ tailWord_8008997) baseStart_8008997 baseEnd_8008997 := by
    simpa [prefixWord, tailWord_8008997, baseEnd_8008997] using wordTrace_append hprefix tailTrace_8008997
  have hstable : (prefixWord ++ tailWord_8008997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8008997).length < 2 ^ (prefixWord ++ tailWord_8008997).sum := by decide
  have hdescent : baseEnd_8008997 < baseStart_8008997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8008997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009034 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_8009034 : Nat := 118140960795 + 8009034 * 2 ^ 59
def prefixEnd_8009034 : Nat := 4983230072969 + 3 ^ 40 * 8009034 * 2
def baseEnd_8009034 : Nat := 4112484020201522851342129

theorem tailTrace_8009034 : CollatzResearch.WordTrace tailWord_8009034 prefixEnd_8009034 4112484020201522851342129 := by
  unfold tailWord_8009034
  simp only [CollatzResearch.WordTrace]
  refine ⟨73028367016661281738368539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194742312044430084635649437 73028367016661281738368539)
  ·
    refine ⟨109542550524991922607552809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73028367016661281738368539 109542550524991922607552809)
    ·
      refine ⟨82156912893743941955664607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109542550524991922607552809 82156912893743941955664607)
      ·
        refine ⟨123235369340615912933496911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82156912893743941955664607 123235369340615912933496911)
        ·
          refine ⟨184853054010923869400245367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123235369340615912933496911 184853054010923869400245367)
          ·
            refine ⟨277279581016385804100368051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184853054010923869400245367 277279581016385804100368051)
            ·
              refine ⟨415919371524578706150552077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277279581016385804100368051 415919371524578706150552077)
              ·
                refine ⟨155969764321717014806457029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415919371524578706150552077 155969764321717014806457029)
                ·
                  refine ⟨29244330810321940276210693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155969764321717014806457029 29244330810321940276210693)
                  ·
                    refine ⟨5483312026935363801789505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29244330810321940276210693 5483312026935363801789505)
                    ·
                      refine ⟨4112484020201522851342129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483312026935363801789505 4112484020201522851342129)
                      ·
                        rfl

theorem cell23_8009034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_8009034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009034 prefixEnd_8009034 := by exact prefixLift 8009034
  have htrace : WordTrace (prefixWord ++ tailWord_8009034) baseStart_8009034 baseEnd_8009034 := by
    simpa [prefixWord, tailWord_8009034, baseEnd_8009034] using wordTrace_append hprefix tailTrace_8009034
  have hstable : (prefixWord ++ tailWord_8009034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009034).length < 2 ^ (prefixWord ++ tailWord_8009034).sum := by decide
  have hdescent : baseEnd_8009034 < baseStart_8009034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009087 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 7, 5]
def baseStart_8009087 : Nat := 118140960795 + 8009087 * 2 ^ 59
def prefixEnd_8009087 : Nat := 4983230072969 + 3 ^ 40 * 8009087 * 2
def baseEnd_8009087 : Nat := 1370837078225403714659795

theorem tailTrace_8009087 : CollatzResearch.WordTrace tailWord_8009087 prefixEnd_8009087 1370837078225403714659795 := by
  unfold tailWord_8009087
  simp only [CollatzResearch.WordTrace]
  refine ⟨292115401135453117005153515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194743600756968744670102343 292115401135453117005153515)
  ·
    refine ⟨438173101703179675507730273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292115401135453117005153515 438173101703179675507730273)
    ·
      refine ⟨328629826277384756630797705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438173101703179675507730273 328629826277384756630797705)
      ·
        refine ⟨246472369708038567473098279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328629826277384756630797705 246472369708038567473098279)
        ·
          refine ⟨369708554562057851209647419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246472369708038567473098279 369708554562057851209647419)
          ·
            refine ⟨554562831843086776814471129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369708554562057851209647419 554562831843086776814471129)
            ·
              refine ⟨415922123882315082610853347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554562831843086776814471129 415922123882315082610853347)
              ·
                refine ⟨623883185823472623916280021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415922123882315082610853347 623883185823472623916280021)
                ·
                  refine ⟨14622262167737639623037813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 623883185823472623916280021 14622262167737639623037813)
                  ·
                    refine ⟨1370837078225403714659795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14622262167737639623037813 1370837078225403714659795)
                    ·
                      rfl

theorem cell23_8009087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_8009087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009087 prefixEnd_8009087 := by exact prefixLift 8009087
  have htrace : WordTrace (prefixWord ++ tailWord_8009087) baseStart_8009087 baseEnd_8009087 := by
    simpa [prefixWord, tailWord_8009087, baseEnd_8009087] using wordTrace_append hprefix tailTrace_8009087
  have hstable : (prefixWord ++ tailWord_8009087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009087).length < 2 ^ (prefixWord ++ tailWord_8009087).sum := by decide
  have hdescent : baseEnd_8009087 < baseStart_8009087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009095 : List Nat := [1, 1, 4, 2, 2, 4, 2, 2, 1, 4]
def baseStart_8009095 : Nat := 118140960795 + 8009095 * 2 ^ 59
def prefixEnd_8009095 : Nat := 4983230072969 + 3 ^ 40 * 8009095 * 2
def baseEnd_8009095 : Nat := 1370838447507149037559783

theorem tailTrace_8009095 : CollatzResearch.WordTrace tailWord_8009095 prefixEnd_8009095 1370838447507149037559783 := by
  unfold tailWord_8009095
  simp only [CollatzResearch.WordTrace]
  refine ⟨292115692919424134371444739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194743795279616089580963159 292115692919424134371444739)
  ·
    refine ⟨438173539379136201557167109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292115692919424134371444739 438173539379136201557167109)
    ·
      refine ⟨82157538633588037791968833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438173539379136201557167109 82157538633588037791968833)
      ·
        refine ⟨61618153975191028343976625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82157538633588037791968833 61618153975191028343976625)
        ·
          refine ⟨46213615481393271257982469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61618153975191028343976625 46213615481393271257982469)
          ·
            refine ⟨8665052902761238360871713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46213615481393271257982469 8665052902761238360871713)
            ·
              refine ⟨6498789677070928770653785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8665052902761238360871713 6498789677070928770653785)
              ·
                refine ⟨4874092257803196577990339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498789677070928770653785 4874092257803196577990339)
                ·
                  refine ⟨7311138386704794866985509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874092257803196577990339 7311138386704794866985509)
                  ·
                    refine ⟨1370838447507149037559783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7311138386704794866985509 1370838447507149037559783)
                    ·
                      rfl

theorem cell23_8009095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_8009095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009095 prefixEnd_8009095 := by exact prefixLift 8009095
  have htrace : WordTrace (prefixWord ++ tailWord_8009095) baseStart_8009095 baseEnd_8009095 := by
    simpa [prefixWord, tailWord_8009095, baseEnd_8009095] using wordTrace_append hprefix tailTrace_8009095
  have hstable : (prefixWord ++ tailWord_8009095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009095).length < 2 ^ (prefixWord ++ tailWord_8009095).sum := by decide
  have hdescent : baseEnd_8009095 < baseStart_8009095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009178 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_8009178 : Nat := 118140960795 + 8009178 * 2 ^ 59
def prefixEnd_8009178 : Nat := 4983230072969 + 3 ^ 40 * 8009178 * 2
def baseEnd_8009178 : Nat := 4112557961415770287941467

theorem tailTrace_8009178 : CollatzResearch.WordTrace tailWord_8009178 prefixEnd_8009178 4112557961415770287941467 := by
  unfold tailWord_8009178
  simp only [CollatzResearch.WordTrace]
  refine ⟨73029680044530859886679047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194745813452082293031144125 73029680044530859886679047)
  ·
    refine ⟨109544520066796289830018571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73029680044530859886679047 109544520066796289830018571)
    ·
      refine ⟨164316780100194434745027857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109544520066796289830018571 164316780100194434745027857)
      ·
        refine ⟨123237585075145826058770893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164316780100194434745027857 123237585075145826058770893)
        ·
          refine ⟨46214094403179684772039085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123237585075145826058770893 46214094403179684772039085)
          ·
            refine ⟨17330285401192381789514657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46214094403179684772039085 17330285401192381789514657)
            ·
              refine ⟨12997714050894286342135993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17330285401192381789514657 12997714050894286342135993)
              ·
                refine ⟨9748285538170714756601995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12997714050894286342135993 9748285538170714756601995)
                ·
                  refine ⟨14622428307256072134902993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748285538170714756601995 14622428307256072134902993)
                  ·
                    refine ⟨10966821230442054101177245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14622428307256072134902993 10966821230442054101177245)
                    ·
                      refine ⟨4112557961415770287941467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10966821230442054101177245 4112557961415770287941467)
                      ·
                        rfl

theorem cell23_8009178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_8009178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009178 prefixEnd_8009178 := by exact prefixLift 8009178
  have htrace : WordTrace (prefixWord ++ tailWord_8009178) baseStart_8009178 baseEnd_8009178 := by
    simpa [prefixWord, tailWord_8009178, baseEnd_8009178] using wordTrace_append hprefix tailTrace_8009178
  have hstable : (prefixWord ++ tailWord_8009178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009178).length < 2 ^ (prefixWord ++ tailWord_8009178).sum := by decide
  have hdescent : baseEnd_8009178 < baseStart_8009178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009181 : List Nat := [1, 4, 3, 1, 1, 2, 4, 7]
def baseStart_8009181 : Nat := 118140960795 + 8009181 * 2 ^ 59
def prefixEnd_8009181 : Nat := 4983230072969 + 3 ^ 40 * 8009181 * 2
def baseEnd_8009181 : Nat := 152317018587323473192739

theorem tailTrace_8009181 : CollatzResearch.WordTrace tailWord_8009181 prefixEnd_8009181 152317018587323473192739 := by
  unfold tailWord_8009181
  simp only [CollatzResearch.WordTrace]
  refine ⟨292118829597112571059075397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194745886398075047372716931 292118829597112571059075397)
  ·
    refine ⟨54772280549458607073576637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292118829597112571059075397 54772280549458607073576637)
    ·
      refine ⟨20539605206046977652591239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54772280549458607073576637 20539605206046977652591239)
      ·
        refine ⟨30809407809070466478886859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20539605206046977652591239 30809407809070466478886859)
        ·
          refine ⟨46214111713605699718330289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30809407809070466478886859 46214111713605699718330289)
          ·
            refine ⟨34660583785204274788747717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46214111713605699718330289 34660583785204274788747717)
            ·
              refine ⟨6498859459725801522890197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34660583785204274788747717 6498859459725801522890197)
              ·
                refine ⟨152317018587323473192739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6498859459725801522890197 152317018587323473192739)
                ·
                  rfl

theorem cell23_8009181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 7].length) (baseStart_8009181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009181 prefixEnd_8009181 := by exact prefixLift 8009181
  have htrace : WordTrace (prefixWord ++ tailWord_8009181) baseStart_8009181 baseEnd_8009181 := by
    simpa [prefixWord, tailWord_8009181, baseEnd_8009181] using wordTrace_append hprefix tailTrace_8009181
  have hstable : (prefixWord ++ tailWord_8009181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009181).length < 2 ^ (prefixWord ++ tailWord_8009181).sum := by decide
  have hdescent : baseEnd_8009181 < baseStart_8009181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009224 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 2, 6]
def baseStart_8009224 : Nat := 118140960795 + 8009224 * 2 ^ 59
def prefixEnd_8009224 : Nat := 4983230072969 + 3 ^ 40 * 8009224 * 2
def baseEnd_8009224 : Nat := 1370860527175292369322085

theorem tailTrace_8009224 : CollatzResearch.WordTrace tailWord_8009224 prefixEnd_8009224 1370860527175292369322085 := by
  unfold tailWord_8009224
  simp only [CollatzResearch.WordTrace]
  refine ⟨146060198967978394701445363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194746931957304526268593817 146060198967978394701445363)
  ·
    refine ⟨219090298451967592052168045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146060198967978394701445363 219090298451967592052168045)
    ·
      refine ⟨82158861919487847019563017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219090298451967592052168045 82158861919487847019563017)
      ·
        refine ⟨61619146439615885264672263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82158861919487847019563017 61619146439615885264672263)
        ·
          refine ⟨92428719659423827897008395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61619146439615885264672263 92428719659423827897008395)
          ·
            refine ⟨138643079489135741845512593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92428719659423827897008395 138643079489135741845512593)
            ·
              refine ⟨103982309616851806384134445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138643079489135741845512593 103982309616851806384134445)
              ·
                refine ⟨38993366106319427394050417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103982309616851806384134445 38993366106319427394050417)
                ·
                  refine ⟨29245024579739570545537813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38993366106319427394050417 29245024579739570545537813)
                  ·
                    refine ⟨1370860527175292369322085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29245024579739570545537813 1370860527175292369322085)
                    ·
                      rfl

theorem cell23_8009224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_8009224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009224 prefixEnd_8009224 := by exact prefixLift 8009224
  have htrace : WordTrace (prefixWord ++ tailWord_8009224) baseStart_8009224 baseEnd_8009224 := by
    simpa [prefixWord, tailWord_8009224, baseEnd_8009224] using wordTrace_append hprefix tailTrace_8009224
  have hstable : (prefixWord ++ tailWord_8009224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009224).length < 2 ^ (prefixWord ++ tailWord_8009224).sum := by decide
  have hdescent : baseEnd_8009224 < baseStart_8009224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009229 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_8009229 : Nat := 118140960795 + 8009229 * 2 ^ 59
def prefixEnd_8009229 : Nat := 4983230072969 + 3 ^ 40 * 8009229 * 2
def baseEnd_8009229 : Nat := 4112584148929149588403733

theorem tailTrace_8009229 : CollatzResearch.WordTrace tailWord_8009229 prefixEnd_8009229 4112584148929149588403733 := by
  unfold tailWord_8009229
  simp only [CollatzResearch.WordTrace]
  refine ⟨292120580300938675256822741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194747053533959116837881827 292120580300938675256822741)
  ·
    refine ⟨6846576100803250201331783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 292120580300938675256822741 6846576100803250201331783)
    ·
      refine ⟨10269864151204875301997675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6846576100803250201331783 10269864151204875301997675)
      ·
        refine ⟨15404796226807312952996513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10269864151204875301997675 15404796226807312952996513)
        ·
          refine ⟨11553597170105484714747385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15404796226807312952996513 11553597170105484714747385)
          ·
            refine ⟨8665197877579113536060539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11553597170105484714747385 8665197877579113536060539)
            ·
              refine ⟨12997796816368670304090809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8665197877579113536060539 12997796816368670304090809)
              ·
                refine ⟨9748347612276502728068107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12997796816368670304090809 9748347612276502728068107)
                ·
                  refine ⟨14622521418414754092102161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748347612276502728068107 14622521418414754092102161)
                  ·
                    refine ⟨10966891063811065569076621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14622521418414754092102161 10966891063811065569076621)
                    ·
                      refine ⟨4112584148929149588403733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10966891063811065569076621 4112584148929149588403733)
                      ·
                        rfl

theorem cell23_8009229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_8009229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009229 prefixEnd_8009229 := by exact prefixLift 8009229
  have htrace : WordTrace (prefixWord ++ tailWord_8009229) baseStart_8009229 baseEnd_8009229 := by
    simpa [prefixWord, tailWord_8009229, baseEnd_8009229] using wordTrace_append hprefix tailTrace_8009229
  have hstable : (prefixWord ++ tailWord_8009229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009229).length < 2 ^ (prefixWord ++ tailWord_8009229).sum := by decide
  have hdescent : baseEnd_8009229 < baseStart_8009229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009235 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 1, 3, 2]
def baseStart_8009235 : Nat := 118140960795 + 8009235 * 2 ^ 59
def prefixEnd_8009235 : Nat := 4983230072969 + 3 ^ 40 * 8009235 * 2
def baseEnd_8009235 : Nat := 4112587229813076564928705

theorem tailTrace_8009235 : CollatzResearch.WordTrace tailWord_8009235 prefixEnd_8009235 4112587229813076564928705 := by
  unfold tailWord_8009235
  simp only [CollatzResearch.WordTrace]
  refine ⟨292120799138916938281541159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194747199425944625521027439 292120799138916938281541159)
  ·
    refine ⟨438181198708375407422311739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292120799138916938281541159 438181198708375407422311739)
    ·
      refine ⟨657271798062563111133467609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438181198708375407422311739 657271798062563111133467609)
      ·
        refine ⟨492953848546922333350100707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657271798062563111133467609 492953848546922333350100707)
        ·
          refine ⟨739430772820383500025151061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492953848546922333350100707 739430772820383500025151061)
          ·
            refine ⟨8665204368988869140919739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 739430772820383500025151061 8665204368988869140919739)
            ·
              refine ⟨12997806553483303711379609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8665204368988869140919739 12997806553483303711379609)
              ·
                refine ⟨9748354915112477783534707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12997806553483303711379609 9748354915112477783534707)
                ·
                  refine ⟨14622532372668716675302061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748354915112477783534707 14622532372668716675302061)
                  ·
                    refine ⟨5483449639750768753238273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14622532372668716675302061 5483449639750768753238273)
                    ·
                      refine ⟨4112587229813076564928705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483449639750768753238273 4112587229813076564928705)
                      ·
                        rfl

theorem cell23_8009235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 3, 2].length) (baseStart_8009235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009235 prefixEnd_8009235 := by exact prefixLift 8009235
  have htrace : WordTrace (prefixWord ++ tailWord_8009235) baseStart_8009235 baseEnd_8009235 := by
    simpa [prefixWord, tailWord_8009235, baseEnd_8009235] using wordTrace_append hprefix tailTrace_8009235
  have hstable : (prefixWord ++ tailWord_8009235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009235).length < 2 ^ (prefixWord ++ tailWord_8009235).sum := by decide
  have hdescent : baseEnd_8009235 < baseStart_8009235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009246 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_8009246 : Nat := 118140960795 + 8009246 * 2 ^ 59
def prefixEnd_8009246 : Nat := 4983230072969 + 3 ^ 40 * 8009246 * 2
def baseEnd_8009246 : Nat := 4112592878100276021891155

theorem tailTrace_8009246 : CollatzResearch.WordTrace tailWord_8009246 prefixEnd_8009246 4112592878100276021891155 := by
  unfold tailWord_8009246
  simp only [CollatzResearch.WordTrace]
  refine ⟨36515150042734635895023949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194747466894584724773461061 36515150042734635895023949)
  ·
    refine ⟨13693181266025488460633981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36515150042734635895023949 13693181266025488460633981)
    ·
      refine ⟨5134942974759558172737743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13693181266025488460633981 5134942974759558172737743)
      ·
        refine ⟨7702414462139337259106615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134942974759558172737743 7702414462139337259106615)
        ·
          refine ⟨11553621693209005888659923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7702414462139337259106615 11553621693209005888659923)
          ·
            refine ⟨17330432539813508832989885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11553621693209005888659923 17330432539813508832989885)
            ·
              refine ⟨6498912202430065812371207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17330432539813508832989885 6498912202430065812371207)
              ·
                refine ⟨9748368303645098718556811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498912202430065812371207 9748368303645098718556811)
                ·
                  refine ⟨14622552455467648077835217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748368303645098718556811 14622552455467648077835217)
                  ·
                    refine ⟨10966914341600736058376413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14622552455467648077835217 10966914341600736058376413)
                    ·
                      refine ⟨4112592878100276021891155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10966914341600736058376413 4112592878100276021891155)
                      ·
                        rfl

theorem cell23_8009246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_8009246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009246 prefixEnd_8009246 := by exact prefixLift 8009246
  have htrace : WordTrace (prefixWord ++ tailWord_8009246) baseStart_8009246 baseEnd_8009246 := by
    simpa [prefixWord, tailWord_8009246, baseEnd_8009246] using wordTrace_append hprefix tailTrace_8009246
  have hstable : (prefixWord ++ tailWord_8009246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009246).length < 2 ^ (prefixWord ++ tailWord_8009246).sum := by decide
  have hdescent : baseEnd_8009246 < baseStart_8009246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009248 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 3, 4, 2]
def baseStart_8009248 : Nat := 118140960795 + 8009248 * 2 ^ 59
def prefixEnd_8009248 : Nat := 4983230072969 + 3 ^ 40 * 8009248 * 2
def baseEnd_8009248 : Nat := 4112593905061585014066145

theorem tailTrace_8009248 : CollatzResearch.WordTrace tailWord_8009248 prefixEnd_8009248 4112593905061585014066145 := by
  unfold tailWord_8009248
  simp only [CollatzResearch.WordTrace]
  refine ⟨146060636643934920750882199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194747515525246561001176265 146060636643934920750882199)
  ·
    refine ⟨219090954965902381126323299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146060636643934920750882199 219090954965902381126323299)
    ·
      refine ⟨328636432448853571689484949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219090954965902381126323299 328636432448853571689484949)
      ·
        refine ⟨15404832771040011172944607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 328636432448853571689484949 15404832771040011172944607)
        ·
          refine ⟨23107249156560016759416911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15404832771040011172944607 23107249156560016759416911)
          ·
            refine ⟨34660873734840025139125367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23107249156560016759416911 34660873734840025139125367)
            ·
              refine ⟨51991310602260037708688051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34660873734840025139125367 51991310602260037708688051)
              ·
                refine ⟨77986965903390056563032077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51991310602260037708688051 77986965903390056563032077)
                ·
                  refine ⟨29245112213771271211137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77986965903390056563032077 29245112213771271211137029)
                  ·
                    refine ⟨5483458540082113352088193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29245112213771271211137029 5483458540082113352088193)
                    ·
                      refine ⟨4112593905061585014066145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483458540082113352088193 4112593905061585014066145)
                      ·
                        rfl

theorem cell23_8009248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_8009248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009248 prefixEnd_8009248 := by exact prefixLift 8009248
  have htrace : WordTrace (prefixWord ++ tailWord_8009248) baseStart_8009248 baseEnd_8009248 := by
    simpa [prefixWord, tailWord_8009248, baseEnd_8009248] using wordTrace_append hprefix tailTrace_8009248
  have hstable : (prefixWord ++ tailWord_8009248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009248).length < 2 ^ (prefixWord ++ tailWord_8009248).sum := by decide
  have hdescent : baseEnd_8009248 < baseStart_8009248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009291 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 4, 5, 2]
def baseStart_8009291 : Nat := 118140960795 + 8009291 * 2 ^ 59
def prefixEnd_8009291 : Nat := 4983230072969 + 3 ^ 40 * 8009291 * 2
def baseEnd_8009291 : Nat := 4112615984729728345828447

theorem tailTrace_8009291 : CollatzResearch.WordTrace tailWord_8009291 prefixEnd_8009291 4112615984729728345828447 := by
  unfold tailWord_8009291
  simp only [CollatzResearch.WordTrace]
  refine ⟨292122841626714059845579727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194748561084476039897053151 292122841626714059845579727)
  ·
    refine ⟨438184262440071089768369591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292122841626714059845579727 438184262440071089768369591)
    ·
      refine ⟨657276393660106634652554387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438184262440071089768369591 657276393660106634652554387)
      ·
        refine ⟨985914590490159951978831581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657276393660106634652554387 985914590490159951978831581)
        ·
          refine ⟨369717971433809981992061843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 985914590490159951978831581 369717971433809981992061843)
          ·
            refine ⟨554576957150714972988092765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369717971433809981992061843 554576957150714972988092765)
            ·
              refine ⟨207966358931518114870534787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554576957150714972988092765 207966358931518114870534787)
              ·
                refine ⟨311949538397277172305802181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207966358931518114870534787 311949538397277172305802181)
                ·
                  refine ⟨58490538449489469807337909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311949538397277172305802181 58490538449489469807337909)
                  ·
                    refine ⟨5483487979639637794437929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58490538449489469807337909 5483487979639637794437929)
                    ·
                      refine ⟨4112615984729728345828447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483487979639637794437929 4112615984729728345828447)
                      ·
                        rfl

theorem cell23_8009291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 5, 2].length) (baseStart_8009291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009291 prefixEnd_8009291 := by exact prefixLift 8009291
  have htrace : WordTrace (prefixWord ++ tailWord_8009291) baseStart_8009291 baseEnd_8009291 := by
    simpa [prefixWord, tailWord_8009291, baseEnd_8009291] using wordTrace_append hprefix tailTrace_8009291
  have hstable : (prefixWord ++ tailWord_8009291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009291).length < 2 ^ (prefixWord ++ tailWord_8009291).sum := by decide
  have hdescent : baseEnd_8009291 < baseStart_8009291 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009321 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_8009321 : Nat := 118140960795 + 8009321 * 2 ^ 59
def prefixEnd_8009321 : Nat := 4983230072969 + 3 ^ 40 * 8009321 * 2
def baseEnd_8009321 : Nat := 4112631389149363228453309

theorem tailTrace_8009321 : CollatzResearch.WordTrace tailWord_8009321 prefixEnd_8009321 4112631389149363228453309 := by
  unfold tailWord_8009321
  simp only [CollatzResearch.WordTrace]
  refine ⟨292123935816605374969171817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194749290544403583312781211 292123935816605374969171817)
  ·
    refine ⟨219092951862454031226878863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292123935816605374969171817 219092951862454031226878863)
    ·
      refine ⟨328639427793681046840318295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219092951862454031226878863 328639427793681046840318295)
      ·
        refine ⟨492959141690521570260477443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328639427793681046840318295 492959141690521570260477443)
        ·
          refine ⟨739438712535782355390716165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492959141690521570260477443 739438712535782355390716165)
          ·
            refine ⟨138644758600459191635759281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 739438712535782355390716165 138644758600459191635759281)
            ·
              refine ⟨103983568950344393726819461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138644758600459191635759281 103983568950344393726819461)
              ·
                refine ⟨19496919178189573823778649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103983568950344393726819461 19496919178189573823778649)
                ·
                  refine ⟨14622689383642180367833987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19496919178189573823778649 14622689383642180367833987)
                  ·
                    refine ⟨21934034075463270551750981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14622689383642180367833987 21934034075463270551750981)
                    ·
                      refine ⟨4112631389149363228453309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21934034075463270551750981 4112631389149363228453309)
                      ·
                        rfl

theorem cell23_8009321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_8009321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009321 prefixEnd_8009321 := by exact prefixLift 8009321
  have htrace : WordTrace (prefixWord ++ tailWord_8009321) baseStart_8009321 baseEnd_8009321 := by
    simpa [prefixWord, tailWord_8009321, baseEnd_8009321] using wordTrace_append hprefix tailTrace_8009321
  have hstable : (prefixWord ++ tailWord_8009321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009321).length < 2 ^ (prefixWord ++ tailWord_8009321).sum := by decide
  have hdescent : baseEnd_8009321 < baseStart_8009321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009358 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_8009358 : Nat := 118140960795 + 8009358 * 2 ^ 59
def prefixEnd_8009358 : Nat := 4983230072969 + 3 ^ 40 * 8009358 * 2
def baseEnd_8009358 : Nat := 4112650387933579583690639

theorem tailTrace_8009358 : CollatzResearch.WordTrace tailWord_8009358 prefixEnd_8009358 4112650387933579583690639 := by
  unfold tailWord_8009358
  simp only [CollatzResearch.WordTrace]
  refine ⟨36515660664683916286033591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194750190211647553525512485 36515660664683916286033591)
  ·
    refine ⟨54773490997025874429050387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36515660664683916286033591 54773490997025874429050387)
    ·
      refine ⟨82160236495538811643575581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54773490997025874429050387 82160236495538811643575581)
      ·
        refine ⟨30810088685827054366340843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82160236495538811643575581 30810088685827054366340843)
        ·
          refine ⟨46215133028740581549511265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30810088685827054366340843 46215133028740581549511265)
          ·
            refine ⟨34661349771555436162133449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46215133028740581549511265 34661349771555436162133449)
            ·
              refine ⟨25996012328666577121600087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34661349771555436162133449 25996012328666577121600087)
              ·
                refine ⟨38994018492999865682400131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25996012328666577121600087 38994018492999865682400131)
                ·
                  refine ⟨58491027739499798523600197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38994018492999865682400131 58491027739499798523600197)
                  ·
                    refine ⟨10967067701156212223175037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58491027739499798523600197 10967067701156212223175037)
                    ·
                      refine ⟨4112650387933579583690639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10967067701156212223175037 4112650387933579583690639)
                      ·
                        rfl

theorem cell23_8009358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_8009358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009358 prefixEnd_8009358 := by exact prefixLift 8009358
  have htrace : WordTrace (prefixWord ++ tailWord_8009358) baseStart_8009358 baseEnd_8009358 := by
    simpa [prefixWord, tailWord_8009358, baseEnd_8009358] using wordTrace_append hprefix tailTrace_8009358
  have hstable : (prefixWord ++ tailWord_8009358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009358).length < 2 ^ (prefixWord ++ tailWord_8009358).sum := by decide
  have hdescent : baseEnd_8009358 < baseStart_8009358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009391 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 3, 5]
def baseStart_8009391 : Nat := 118140960795 + 8009391 * 2 ^ 59
def prefixEnd_8009391 : Nat := 4983230072969 + 3 ^ 40 * 8009391 * 2
def baseEnd_8009391 : Nat := 1370889110931725984859329

theorem tailTrace_8009391 : CollatzResearch.WordTrace tailWord_8009391 prefixEnd_8009391 1370889110931725984859329 := by
  unfold tailWord_8009391
  simp only [CollatzResearch.WordTrace]
  refine ⟨292126488926351776924220027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194750992617567851282813351 292126488926351776924220027)
  ·
    refine ⟨438189733389527665386330041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292126488926351776924220027 438189733389527665386330041)
    ·
      refine ⟨328642300042145749039747531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438189733389527665386330041 328642300042145749039747531)
      ·
        refine ⟨492963450063218623559621297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328642300042145749039747531 492963450063218623559621297)
        ·
          refine ⟨369722587547413967669715973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492963450063218623559621297 369722587547413967669715973)
          ·
            refine ⟨69322985165140118938071745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369722587547413967669715973 69322985165140118938071745)
            ·
              refine ⟨51992238873855089203553809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69322985165140118938071745 51992238873855089203553809)
              ·
                refine ⟨38994179155391316902665357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51992238873855089203553809 38994179155391316902665357)
                ·
                  refine ⟨14622817183271743838499509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38994179155391316902665357 14622817183271743838499509)
                  ·
                    refine ⟨1370889110931725984859329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14622817183271743838499509 1370889110931725984859329)
                    ·
                      rfl

theorem cell23_8009391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_8009391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009391 prefixEnd_8009391 := by exact prefixLift 8009391
  have htrace : WordTrace (prefixWord ++ tailWord_8009391) baseStart_8009391 baseEnd_8009391 := by
    simpa [prefixWord, tailWord_8009391, baseEnd_8009391] using wordTrace_append hprefix tailTrace_8009391
  have hstable : (prefixWord ++ tailWord_8009391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009391).length < 2 ^ (prefixWord ++ tailWord_8009391).sum := by decide
  have hdescent : baseEnd_8009391 < baseStart_8009391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009415 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_8009415 : Nat := 118140960795 + 8009415 * 2 ^ 59
def prefixEnd_8009415 : Nat := 4983230072969 + 3 ^ 40 * 8009415 * 2
def baseEnd_8009415 : Nat := 4112679656330885860677877

theorem tailTrace_8009415 : CollatzResearch.WordTrace tailWord_8009415 prefixEnd_8009415 4112679656330885860677877 := by
  unfold tailWord_8009415
  simp only [CollatzResearch.WordTrace]
  refine ⟨292127364278264829023093699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194751576185509886015395799 292127364278264829023093699)
  ·
    refine ⟨438191046417397243534640549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292127364278264829023093699 438191046417397243534640549)
    ·
      refine ⟨82160821203261983162745103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438191046417397243534640549 82160821203261983162745103)
      ·
        refine ⟨123241231804892974744117655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82160821203261983162745103 123241231804892974744117655)
        ·
          refine ⟨184861847707339462116176483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123241231804892974744117655 184861847707339462116176483)
          ·
            refine ⟨277292771561009193174264725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184861847707339462116176483 277292771561009193174264725)
            ·
              refine ⟨12998098666922305930043659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 277292771561009193174264725 12998098666922305930043659)
              ·
                refine ⟨19497148000383458895065489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12998098666922305930043659 19497148000383458895065489)
                ·
                  refine ⟨14622861000287594171299117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19497148000383458895065489 14622861000287594171299117)
                  ·
                    refine ⟨5483572875107847814237169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14622861000287594171299117 5483572875107847814237169)
                    ·
                      refine ⟨4112679656330885860677877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483572875107847814237169 4112679656330885860677877)
                      ·
                        rfl

theorem cell23_8009415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_8009415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009415 prefixEnd_8009415 := by exact prefixLift 8009415
  have htrace : WordTrace (prefixWord ++ tailWord_8009415) baseStart_8009415 baseEnd_8009415 := by
    simpa [prefixWord, tailWord_8009415, baseEnd_8009415] using wordTrace_append hprefix tailTrace_8009415
  have hstable : (prefixWord ++ tailWord_8009415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009415).length < 2 ^ (prefixWord ++ tailWord_8009415).sum := by decide
  have hdescent : baseEnd_8009415 < baseStart_8009415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009422 : List Nat := [4, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_8009422 : Nat := 118140960795 + 8009422 * 2 ^ 59
def prefixEnd_8009422 : Nat := 4983230072969 + 3 ^ 40 * 8009422 * 2
def baseEnd_8009422 : Nat := 4112683250695467333290345

theorem tailTrace_8009422 : CollatzResearch.WordTrace tailWord_8009422 prefixEnd_8009422 4112683250695467333290345 := by
  unfold tailWord_8009422
  simp only [CollatzResearch.WordTrace]
  refine ⟨36515952448654933652324815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194751746392826312812399013 36515952448654933652324815)
  ·
    refine ⟨54773928672982400478487223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36515952448654933652324815 54773928672982400478487223)
    ·
      refine ⟨82160893009473600717730835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54773928672982400478487223 82160893009473600717730835)
      ·
        refine ⟨123241339514210401076596253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82160893009473600717730835 123241339514210401076596253)
        ·
          refine ⟨46215502317828900403723595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123241339514210401076596253 46215502317828900403723595)
          ·
            refine ⟨69323253476743350605585393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46215502317828900403723595 69323253476743350605585393)
            ·
              refine ⟨51992440107557512954189045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69323253476743350605585393 51992440107557512954189045)
              ·
                refine ⟨4874291260083516839455223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51992440107557512954189045 4874291260083516839455223)
                ·
                  refine ⟨7311436890125275259182835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874291260083516839455223 7311436890125275259182835)
                  ·
                    refine ⟨10967155335187912888774253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7311436890125275259182835 10967155335187912888774253)
                    ·
                      refine ⟨4112683250695467333290345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10967155335187912888774253 4112683250695467333290345)
                      ·
                        rfl

theorem cell23_8009422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_8009422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009422 prefixEnd_8009422 := by exact prefixLift 8009422
  have htrace : WordTrace (prefixWord ++ tailWord_8009422) baseStart_8009422 baseEnd_8009422 := by
    simpa [prefixWord, tailWord_8009422, baseEnd_8009422] using wordTrace_append hprefix tailTrace_8009422
  have hstable : (prefixWord ++ tailWord_8009422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009422).length < 2 ^ (prefixWord ++ tailWord_8009422).sum := by decide
  have hdescent : baseEnd_8009422 < baseStart_8009422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009425 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 1, 5]
def baseStart_8009425 : Nat := 118140960795 + 8009425 * 2 ^ 59
def prefixEnd_8009425 : Nat := 4983230072969 + 3 ^ 40 * 8009425 * 2
def baseEnd_8009425 : Nat := 1370894930379143607184277

theorem tailTrace_8009425 : CollatzResearch.WordTrace tailWord_8009425 prefixEnd_8009425 1370894930379143607184277 := by
  unfold tailWord_8009425
  simp only [CollatzResearch.WordTrace]
  refine ⟨292127729008228600730957729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194751819338819067153971819 292127729008228600730957729)
  ·
    refine ⟨219095796756171450548218297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292127729008228600730957729 219095796756171450548218297)
    ·
      refine ⟨164321847567128587911163723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219095796756171450548218297 164321847567128587911163723)
      ·
        refine ⟨246482771350692881866745585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164321847567128587911163723 246482771350692881866745585)
        ·
          refine ⟨184862078513019661400059189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246482771350692881866745585 184862078513019661400059189)
          ·
            refine ⟨17330819860595593256255549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184862078513019661400059189 17330819860595593256255549)
            ·
              refine ⟨6499057447723347471095831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17330819860595593256255549 6499057447723347471095831)
              ·
                refine ⟨9748586171585021206643747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499057447723347471095831 9748586171585021206643747)
                ·
                  refine ⟨14622879257377531809965621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748586171585021206643747 14622879257377531809965621)
                  ·
                    refine ⟨1370894930379143607184277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14622879257377531809965621 1370894930379143607184277)
                    ·
                      rfl

theorem cell23_8009425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_8009425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009425 prefixEnd_8009425 := by exact prefixLift 8009425
  have htrace : WordTrace (prefixWord ++ tailWord_8009425) baseStart_8009425 baseEnd_8009425 := by
    simpa [prefixWord, tailWord_8009425, baseEnd_8009425] using wordTrace_append hprefix tailTrace_8009425
  have hstable : (prefixWord ++ tailWord_8009425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009425).length < 2 ^ (prefixWord ++ tailWord_8009425).sum := by decide
  have hdescent : baseEnd_8009425 < baseStart_8009425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009451 : List Nat := [1, 1, 1, 1, 2, 4, 5, 8]
def baseStart_8009451 : Nat := 118140960795 + 8009451 * 2 ^ 59
def prefixEnd_8009451 : Nat := 4983230072969 + 3 ^ 40 * 8009451 * 2
def baseEnd_8009451 : Nat := 152322153393868434067693

theorem tailTrace_8009451 : CollatzResearch.WordTrace tailWord_8009451 prefixEnd_8009451 152322153393868434067693 := by
  unfold tailWord_8009451
  simp only [CollatzResearch.WordTrace]
  refine ⟨292128677306134407171404207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194752451537422938114269471 292128677306134407171404207)
  ·
    refine ⟨438193015959201610757106311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292128677306134407171404207 438193015959201610757106311)
    ·
      refine ⟨657289523938802416135659467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438193015959201610757106311 657289523938802416135659467)
      ·
        refine ⟨985934285908203624203489201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657289523938802416135659467 985934285908203624203489201)
        ·
          refine ⟨739450714431152718152616901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 985934285908203624203489201 739450714431152718152616901)
          ·
            refine ⟨138647008955841134653615669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 739450714431152718152616901 138647008955841134653615669)
            ·
              refine ⟨12998157089610106373776469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138647008955841134653615669 12998157089610106373776469)
              ·
                refine ⟨152322153393868434067693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12998157089610106373776469 152322153393868434067693)
                ·
                  rfl

theorem cell23_8009451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 8].length) (baseStart_8009451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009451 prefixEnd_8009451 := by exact prefixLift 8009451
  have htrace : WordTrace (prefixWord ++ tailWord_8009451) baseStart_8009451 baseEnd_8009451 := by
    simpa [prefixWord, tailWord_8009451, baseEnd_8009451] using wordTrace_append hprefix tailTrace_8009451
  have hstable : (prefixWord ++ tailWord_8009451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009451).length < 2 ^ (prefixWord ++ tailWord_8009451).sum := by decide
  have hdescent : baseEnd_8009451 < baseStart_8009451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009462 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_8009462 : Nat := 118140960795 + 8009462 * 2 ^ 59
def prefixEnd_8009462 : Nat := 4983230072969 + 3 ^ 40 * 8009462 * 2
def baseEnd_8009462 : Nat := 4112703789921647176790161

theorem tailTrace_8009462 : CollatzResearch.WordTrace tailWord_8009462 prefixEnd_8009462 4112703789921647176790161 := by
  unfold tailWord_8009462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258067406818409753128415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194752719006063037366703093 18258067406818409753128415)
  ·
    refine ⟨27387101110227614629692623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18258067406818409753128415 27387101110227614629692623)
    ·
      refine ⟨41080651665341421944538935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27387101110227614629692623 41080651665341421944538935)
      ·
        refine ⟨61620977498012132916808403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41080651665341421944538935 61620977498012132916808403)
        ·
          refine ⟨92431466247018199375212605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61620977498012132916808403 92431466247018199375212605)
          ·
            refine ⟨34661799842631824765704727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92431466247018199375212605 34661799842631824765704727)
            ·
              refine ⟨51992699763947737148557091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34661799842631824765704727 51992699763947737148557091)
              ·
                refine ⟨77989049645921605722835637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51992699763947737148557091 77989049645921605722835637)
                ·
                  refine ⟨7311473404305150536515841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77989049645921605722835637 7311473404305150536515841)
                  ·
                    refine ⟨5483605053228862902386881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7311473404305150536515841 5483605053228862902386881)
                    ·
                      refine ⟨4112703789921647176790161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483605053228862902386881 4112703789921647176790161)
                      ·
                        rfl

theorem cell23_8009462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_8009462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009462 prefixEnd_8009462 := by exact prefixLift 8009462
  have htrace : WordTrace (prefixWord ++ tailWord_8009462) baseStart_8009462 baseEnd_8009462 := by
    simpa [prefixWord, tailWord_8009462, baseEnd_8009462] using wordTrace_append hprefix tailTrace_8009462
  have hstable : (prefixWord ++ tailWord_8009462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009462).length < 2 ^ (prefixWord ++ tailWord_8009462).sum := by decide
  have hdescent : baseEnd_8009462 < baseStart_8009462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009468 : List Nat := [2, 2, 2, 1, 3, 1, 5, 7]
def baseStart_8009468 : Nat := 118140960795 + 8009468 * 2 ^ 59
def prefixEnd_8009468 : Nat := 4983230072969 + 3 ^ 40 * 8009468 * 2
def baseEnd_8009468 : Nat := 152322476696502746419079

theorem tailTrace_8009468 : CollatzResearch.WordTrace tailWord_8009468 prefixEnd_8009468 152322476696502746419079 := by
  unfold tailWord_8009468
  simp only [CollatzResearch.WordTrace]
  refine ⟨146064648673536409537386529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194752864898048546049848705 146064648673536409537386529)
  ·
    refine ⟨109548486505152307153039897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146064648673536409537386529 109548486505152307153039897)
    ·
      refine ⟨82161364878864230364779923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109548486505152307153039897 82161364878864230364779923)
      ·
        refine ⟨123242047318296345547169885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82161364878864230364779923 123242047318296345547169885)
        ·
          refine ⟨46215767744361129580188707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123242047318296345547169885 46215767744361129580188707)
          ·
            refine ⟨69323651616541694370283061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46215767744361129580188707 69323651616541694370283061)
            ·
              refine ⟨6499092339050783847214037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69323651616541694370283061 6499092339050783847214037)
              ·
                refine ⟨152322476696502746419079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6499092339050783847214037 152322476696502746419079)
                ·
                  rfl

theorem cell23_8009468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 7].length) (baseStart_8009468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009468 prefixEnd_8009468 := by exact prefixLift 8009468
  have htrace : WordTrace (prefixWord ++ tailWord_8009468) baseStart_8009468 baseEnd_8009468 := by
    simpa [prefixWord, tailWord_8009468, baseEnd_8009468] using wordTrace_append hprefix tailTrace_8009468
  have hstable : (prefixWord ++ tailWord_8009468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009468).length < 2 ^ (prefixWord ++ tailWord_8009468).sum := by decide
  have hdescent : baseEnd_8009468 < baseStart_8009468 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009479 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_8009479 : Nat := 118140960795 + 8009479 * 2 ^ 59
def prefixEnd_8009479 : Nat := 4983230072969 + 3 ^ 40 * 8009479 * 2
def baseEnd_8009479 : Nat := 4112712519092773610277583

theorem tailTrace_8009479 : CollatzResearch.WordTrace tailWord_8009479 prefixEnd_8009479 4112712519092773610277583 := by
  unfold tailWord_8009479
  simp only [CollatzResearch.WordTrace]
  refine ⟨292129698550032967953423491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194753132366688645302282327 292129698550032967953423491)
  ·
    refine ⟨438194547825049451930135237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292129698550032967953423491 438194547825049451930135237)
    ·
      refine ⟨82161477717196772236900357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438194547825049451930135237 82161477717196772236900357)
      ·
        refine ⟨15405277071974394794418817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82161477717196772236900357 15405277071974394794418817)
        ·
          refine ⟨11553957803980796095814113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15405277071974394794418817 11553957803980796095814113)
          ·
            refine ⟨8665468352985597071860585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11553957803980796095814113 8665468352985597071860585)
            ·
              refine ⟨6499101264739197803895439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8665468352985597071860585 6499101264739197803895439)
              ·
                refine ⟨9748651897108796705843159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499101264739197803895439 9748651897108796705843159)
                ·
                  refine ⟨14622977845663195058764739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748651897108796705843159 14622977845663195058764739)
                  ·
                    refine ⟨21934466768494792588147109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14622977845663195058764739 21934466768494792588147109)
                    ·
                      refine ⟨4112712519092773610277583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21934466768494792588147109 4112712519092773610277583)
                      ·
                        rfl

theorem cell23_8009479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_8009479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009479 prefixEnd_8009479 := by exact prefixLift 8009479
  have htrace : WordTrace (prefixWord ++ tailWord_8009479) baseStart_8009479 baseEnd_8009479 := by
    simpa [prefixWord, tailWord_8009479, baseEnd_8009479] using wordTrace_append hprefix tailTrace_8009479
  have hstable : (prefixWord ++ tailWord_8009479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009479).length < 2 ^ (prefixWord ++ tailWord_8009479).sum := by decide
  have hdescent : baseEnd_8009479 < baseStart_8009479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009482 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_8009482 : Nat := 118140960795 + 8009482 * 2 ^ 59
def prefixEnd_8009482 : Nat := 4983230072969 + 3 ^ 40 * 8009482 * 2
def baseEnd_8009482 : Nat := 4112714059534737098540069

theorem tailTrace_8009482 : CollatzResearch.WordTrace tailWord_8009482 prefixEnd_8009482 4112714059534737098540069 := by
  unfold tailWord_8009482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73032451992255524866445675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194753205312681399643855133 73032451992255524866445675)
  ·
    refine ⟨109548677988383287299668513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73032451992255524866445675 109548677988383287299668513)
    ·
      refine ⟨82161508491287465474751385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109548677988383287299668513 82161508491287465474751385)
      ·
        refine ⟨61621131368465599106063539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82161508491287465474751385 61621131368465599106063539)
        ·
          refine ⟨92431697052698398659095309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61621131368465599106063539 92431697052698398659095309)
          ·
            refine ⟨34661886394761899497160741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92431697052698398659095309 34661886394761899497160741)
            ·
              refine ⟨6499103699017856155717639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34661886394761899497160741 6499103699017856155717639)
              ·
                refine ⟨9748655548526784233576459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499103699017856155717639 9748655548526784233576459)
                ·
                  refine ⟨14622983322790176350364689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748655548526784233576459 14622983322790176350364689)
                  ·
                    refine ⟨10967237492092632262773517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14622983322790176350364689 10967237492092632262773517)
                    ·
                      refine ⟨4112714059534737098540069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10967237492092632262773517 4112714059534737098540069)
                      ·
                        rfl

theorem cell23_8009482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_8009482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009482 prefixEnd_8009482 := by exact prefixLift 8009482
  have htrace : WordTrace (prefixWord ++ tailWord_8009482) baseStart_8009482 baseEnd_8009482 := by
    simpa [prefixWord, tailWord_8009482, baseEnd_8009482] using wordTrace_append hprefix tailTrace_8009482
  have hstable : (prefixWord ++ tailWord_8009482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009482).length < 2 ^ (prefixWord ++ tailWord_8009482).sum := by decide
  have hdescent : baseEnd_8009482 < baseStart_8009482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009491 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 5]
def baseStart_8009491 : Nat := 118140960795 + 8009491 * 2 ^ 59
def prefixEnd_8009491 : Nat := 4983230072969 + 3 ^ 40 * 8009491 * 2
def baseEnd_8009491 : Nat := 4112718680860627563327527

theorem tailTrace_8009491 : CollatzResearch.WordTrace tailWord_8009491 prefixEnd_8009491 4112718680860627563327527 := by
  unfold tailWord_8009491
  simp only [CollatzResearch.WordTrace]
  refine ⟨292130136225989494002860327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194753424150659662668573551 292130136225989494002860327)
  ·
    refine ⟨438195204338984241004290491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292130136225989494002860327 438195204338984241004290491)
    ·
      refine ⟨657292806508476361506435737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438195204338984241004290491 657292806508476361506435737)
      ·
        refine ⟨492969604881357271129826803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657292806508476361506435737 492969604881357271129826803)
        ·
          refine ⟨739454407322035906694740205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492969604881357271129826803 739454407322035906694740205)
          ·
            refine ⟨277295402745763465010527577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 739454407322035906694740205 277295402745763465010527577)
            ·
              refine ⟨207971552059322598757895683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277295402745763465010527577 207971552059322598757895683)
              ·
                refine ⟨311957328088983898136843525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207971552059322598757895683 311957328088983898136843525)
                ·
                  refine ⟨58491999016684480900658161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311957328088983898136843525 58491999016684480900658161)
                  ·
                    refine ⟨43868999262513360675493621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58491999016684480900658161 43868999262513360675493621)
                    ·
                      refine ⟨4112718680860627563327527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43868999262513360675493621 4112718680860627563327527)
                      ·
                        rfl

theorem cell23_8009491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_8009491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009491 prefixEnd_8009491 := by exact prefixLift 8009491
  have htrace : WordTrace (prefixWord ++ tailWord_8009491) baseStart_8009491 baseEnd_8009491 := by
    simpa [prefixWord, tailWord_8009491, baseEnd_8009491] using wordTrace_append hprefix tailTrace_8009491
  have hstable : (prefixWord ++ tailWord_8009491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009491).length < 2 ^ (prefixWord ++ tailWord_8009491).sum := by decide
  have hdescent : baseEnd_8009491 < baseStart_8009491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009512 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_8009512 : Nat := 118140960795 + 8009512 * 2 ^ 59
def prefixEnd_8009512 : Nat := 4983230072969 + 3 ^ 40 * 8009512 * 2
def baseEnd_8009512 : Nat := 4112729463954371981164931

theorem tailTrace_8009512 : CollatzResearch.WordTrace tailWord_8009512 prefixEnd_8009512 4112729463954371981164931 := by
  unfold tailWord_8009512
  simp only [CollatzResearch.WordTrace]
  refine ⟨146065451079456707294687395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194753934772608943059583193 146065451079456707294687395)
  ·
    refine ⟨219098176619185060942031093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146065451079456707294687395 219098176619185060942031093)
    ·
      refine ⟨20540454058048599463315415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219098176619185060942031093 20540454058048599463315415)
      ·
        refine ⟨30810681087072899194973123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20540454058048599463315415 30810681087072899194973123)
        ·
          refine ⟨46216021630609348792459685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30810681087072899194973123 46216021630609348792459685)
          ·
            refine ⟨8665504055739252898586191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46216021630609348792459685 8665504055739252898586191)
            ·
              refine ⟨12998256083608879347879287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8665504055739252898586191 12998256083608879347879287)
              ·
                refine ⟨19497384125413319021818931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12998256083608879347879287 19497384125413319021818931)
                ·
                  refine ⟨29246076188119978532728397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19497384125413319021818931 29246076188119978532728397)
                  ·
                    refine ⟨10967278570544991949773149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29246076188119978532728397 10967278570544991949773149)
                    ·
                      refine ⟨4112729463954371981164931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10967278570544991949773149 4112729463954371981164931)
                      ·
                        rfl

theorem cell23_8009512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_8009512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009512 prefixEnd_8009512 := by exact prefixLift 8009512
  have htrace : WordTrace (prefixWord ++ tailWord_8009512) baseStart_8009512 baseEnd_8009512 := by
    simpa [prefixWord, tailWord_8009512, baseEnd_8009512] using wordTrace_append hprefix tailTrace_8009512
  have hstable : (prefixWord ++ tailWord_8009512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009512).length < 2 ^ (prefixWord ++ tailWord_8009512).sum := by decide
  have hdescent : baseEnd_8009512 < baseStart_8009512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009522 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_8009522 : Nat := 118140960795 + 8009522 * 2 ^ 59
def prefixEnd_8009522 : Nat := 4983230072969 + 3 ^ 40 * 8009522 * 2
def baseEnd_8009522 : Nat := 4112734598760916942039885

theorem tailTrace_8009522 : CollatzResearch.WordTrace tailWord_8009522 prefixEnd_8009522 4112734598760916942039885 := by
  unfold tailWord_8009522
  simp only [CollatzResearch.WordTrace]
  refine ⟨73032816722219296574309705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194754177925918124198159213 73032816722219296574309705)
  ·
    refine ⟨54774612541664472430732279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73032816722219296574309705 54774612541664472430732279)
    ·
      refine ⟨82161918812496708646098419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54774612541664472430732279 82161918812496708646098419)
      ·
        refine ⟨123242878218745062969147629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82161918812496708646098419 123242878218745062969147629)
        ·
          refine ⟨46216079332029398613430361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123242878218745062969147629 46216079332029398613430361)
          ·
            refine ⟨34662059499022048960072771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46216079332029398613430361 34662059499022048960072771)
            ·
              refine ⟨51993089248533073440109157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34662059499022048960072771 51993089248533073440109157)
              ·
                refine ⟨9748704234099951270020467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51993089248533073440109157 9748704234099951270020467)
                ·
                  refine ⟨14623056351149926905030701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748704234099951270020467 14623056351149926905030701)
                  ·
                    refine ⟨5483646131681222589386513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14623056351149926905030701 5483646131681222589386513)
                    ·
                      refine ⟨4112734598760916942039885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483646131681222589386513 4112734598760916942039885)
                      ·
                        rfl

theorem cell23_8009522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_8009522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009522 prefixEnd_8009522 := by exact prefixLift 8009522
  have htrace : WordTrace (prefixWord ++ tailWord_8009522) baseStart_8009522 baseEnd_8009522 := by
    simpa [prefixWord, tailWord_8009522, baseEnd_8009522] using wordTrace_append hprefix tailTrace_8009522
  have hstable : (prefixWord ++ tailWord_8009522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009522).length < 2 ^ (prefixWord ++ tailWord_8009522).sum := by decide
  have hdescent : baseEnd_8009522 < baseStart_8009522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009552 : List Nat := [2, 1, 1, 1, 1, 4, 1, 6, 2, 2, 2]
def baseStart_8009552 : Nat := 118140960795 + 8009552 * 2 ^ 59
def prefixEnd_8009552 : Nat := 4983230072969 + 3 ^ 40 * 8009552 * 2
def baseEnd_8009552 : Nat := 4112750003180551824664747

theorem tailTrace_8009552 : CollatzResearch.WordTrace tailWord_8009552 prefixEnd_8009552 4112750003180551824664747 := by
  unfold tailWord_8009552
  simp only [CollatzResearch.WordTrace]
  refine ⟨146066180539384250710415455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194754907385845667613887273 146066180539384250710415455)
  ·
    refine ⟨219099270809076376065623183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146066180539384250710415455 219099270809076376065623183)
    ·
      refine ⟨328648906213614564098434775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219099270809076376065623183 328648906213614564098434775)
      ·
        refine ⟨492973359320421846147652163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328648906213614564098434775 492973359320421846147652163)
        ·
          refine ⟨739460038980632769221478245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492973359320421846147652163 739460038980632769221478245)
          ·
            refine ⟨138648757308868644229027171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 739460038980632769221478245 138648757308868644229027171)
            ·
              refine ⟨207973135963302966343540757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138648757308868644229027171 207973135963302966343540757)
              ·
                refine ⟨9748740748279826547353473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207973135963302966343540757 9748740748279826547353473)
                ·
                  refine ⟨7311555561209869910515105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9748740748279826547353473 7311555561209869910515105)
                  ·
                    refine ⟨5483666670907402432886329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7311555561209869910515105 5483666670907402432886329)
                    ·
                      refine ⟨4112750003180551824664747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483666670907402432886329 4112750003180551824664747)
                      ·
                        rfl

theorem cell23_8009552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2, 2, 2].length) (baseStart_8009552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009552 prefixEnd_8009552 := by exact prefixLift 8009552
  have htrace : WordTrace (prefixWord ++ tailWord_8009552) baseStart_8009552 baseEnd_8009552 := by
    simpa [prefixWord, tailWord_8009552, baseEnd_8009552] using wordTrace_append hprefix tailTrace_8009552
  have hstable : (prefixWord ++ tailWord_8009552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009552).length < 2 ^ (prefixWord ++ tailWord_8009552).sum := by decide
  have hdescent : baseEnd_8009552 < baseStart_8009552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009625 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 1, 6, 2]
def baseStart_8009625 : Nat := 118140960795 + 8009625 * 2 ^ 59
def prefixEnd_8009625 : Nat := 4983230072969 + 3 ^ 40 * 8009625 * 2
def baseEnd_8009625 : Nat := 4112787487268330039051911

theorem tailTrace_8009625 : CollatzResearch.WordTrace tailWord_8009625 prefixEnd_8009625 4112787487268330039051911 := by
  unfold tailWord_8009625
  simp only [CollatzResearch.WordTrace]
  refine ⟨292135023607504034888238329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194756682405002689925492219 292135023607504034888238329)
  ·
    refine ⟨219101267705628026166178747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292135023607504034888238329 219101267705628026166178747)
    ·
      refine ⟨328651901558442039249268121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219101267705628026166178747 328651901558442039249268121)
      ·
        refine ⟨246488926168831529436951091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328651901558442039249268121 246488926168831529436951091)
        ·
          refine ⟨369733389253247294155426637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246488926168831529436951091 369733389253247294155426637)
          ·
            refine ⟨138650020969967735308284989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369733389253247294155426637 138650020969967735308284989)
            ·
              refine ⟨51993757863737900740606871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138650020969967735308284989 51993757863737900740606871)
              ·
                refine ⟨77990636795606851110910307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51993757863737900740606871 77990636795606851110910307)
                ·
                  refine ⟨116985955193410276666365461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77990636795606851110910307 116985955193410276666365461)
                  ·
                    refine ⟨5483716649691106718735881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116985955193410276666365461 5483716649691106718735881)
                    ·
                      refine ⟨4112787487268330039051911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483716649691106718735881 4112787487268330039051911)
                      ·
                        rfl

theorem cell23_8009625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_8009625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009625 prefixEnd_8009625 := by exact prefixLift 8009625
  have htrace : WordTrace (prefixWord ++ tailWord_8009625) baseStart_8009625 baseEnd_8009625 := by
    simpa [prefixWord, tailWord_8009625, baseEnd_8009625] using wordTrace_append hprefix tailTrace_8009625
  have hstable : (prefixWord ++ tailWord_8009625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009625).length < 2 ^ (prefixWord ++ tailWord_8009625).sum := by decide
  have hdescent : baseEnd_8009625 < baseStart_8009625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009703 : List Nat := [1, 1, 5, 2, 4, 1, 1, 3, 1, 4]
def baseStart_8009703 : Nat := 118140960795 + 8009703 * 2 ^ 59
def prefixEnd_8009703 : Nat := 4983230072969 + 3 ^ 40 * 8009703 * 2
def baseEnd_8009703 : Nat := 1370942512919793577958851

theorem tailTrace_8009703 : CollatzResearch.WordTrace tailWord_8009703 prefixEnd_8009703 1370942512919793577958851 := by
  unfold tailWord_8009703
  simp only [CollatzResearch.WordTrace]
  refine ⟨292137868501221454209577763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194758579000814302806385175 292137868501221454209577763)
  ·
    refine ⟨438206802751832181314366645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292137868501221454209577763 438206802751832181314366645)
    ·
      refine ⟨41081887757984266998221873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 438206802751832181314366645 41081887757984266998221873)
      ·
        refine ⟨30811415818488200248666405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41081887757984266998221873 30811415818488200248666405)
        ·
          refine ⟨5777140465966537546624951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30811415818488200248666405 5777140465966537546624951)
          ·
            refine ⟨8665710698949806319937427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777140465966537546624951 8665710698949806319937427)
            ·
              refine ⟨12998566048424709479906141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8665710698949806319937427 12998566048424709479906141)
              ·
                refine ⟨4874462268159266054964803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12998566048424709479906141 4874462268159266054964803)
                ·
                  refine ⟨7311693402238899082447205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874462268159266054964803 7311693402238899082447205)
                  ·
                    refine ⟨1370942512919793577958851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7311693402238899082447205 1370942512919793577958851)
                    ·
                      rfl

theorem cell23_8009703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_8009703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009703 prefixEnd_8009703 := by exact prefixLift 8009703
  have htrace : WordTrace (prefixWord ++ tailWord_8009703) baseStart_8009703 baseEnd_8009703 := by
    simpa [prefixWord, tailWord_8009703, baseEnd_8009703] using wordTrace_append hprefix tailTrace_8009703
  have hstable : (prefixWord ++ tailWord_8009703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009703).length < 2 ^ (prefixWord ++ tailWord_8009703).sum := by decide
  have hdescent : baseEnd_8009703 < baseStart_8009703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009726 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_8009726 : Nat := 118140960795 + 8009726 * 2 ^ 59
def prefixEnd_8009726 : Nat := 4983230072969 + 3 ^ 40 * 8009726 * 2
def baseEnd_8009726 : Nat := 4112839348814434143888947

theorem tailTrace_8009726 : CollatzResearch.WordTrace tailWord_8009726 prefixEnd_8009726 4112839348814434143888947 := by
  unfold tailWord_8009726
  simp only [CollatzResearch.WordTrace]
  refine ⟨36517338422517266142208129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194759138253425419425110021 36517338422517266142208129)
  ·
    refine ⟨27388003816887949606656097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36517338422517266142208129 27388003816887949606656097)
    ·
      refine ⟨20541002862665962204992073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27388003816887949606656097 20541002862665962204992073)
      ·
        refine ⟨15405752146999471653744055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20541002862665962204992073 15405752146999471653744055)
        ·
          refine ⟨23108628220499207480616083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15405752146999471653744055 23108628220499207480616083)
          ·
            refine ⟨34662942330748811220924125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23108628220499207480616083 34662942330748811220924125)
            ·
              refine ⟨12998603374030804207846547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34662942330748811220924125 12998603374030804207846547)
              ·
                refine ⟨19497905061046206311769821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12998603374030804207846547 19497905061046206311769821)
                ·
                  refine ⟨7311714397892327366913683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19497905061046206311769821 7311714397892327366913683)
                  ·
                    refine ⟨10967571596838491050370525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7311714397892327366913683 10967571596838491050370525)
                    ·
                      refine ⟨4112839348814434143888947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10967571596838491050370525 4112839348814434143888947)
                      ·
                        rfl

theorem cell23_8009726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_8009726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009726 prefixEnd_8009726 := by exact prefixLift 8009726
  have htrace : WordTrace (prefixWord ++ tailWord_8009726) baseStart_8009726 baseEnd_8009726 := by
    simpa [prefixWord, tailWord_8009726, baseEnd_8009726] using wordTrace_append hprefix tailTrace_8009726
  have hstable : (prefixWord ++ tailWord_8009726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009726).length < 2 ^ (prefixWord ++ tailWord_8009726).sum := by decide
  have hdescent : baseEnd_8009726 < baseStart_8009726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009752 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_8009752 : Nat := 118140960795 + 8009752 * 2 ^ 59
def prefixEnd_8009752 : Nat := 4983230072969 + 3 ^ 40 * 8009752 * 2
def baseEnd_8009752 : Nat := 4112852699311451042163827

theorem tailTrace_8009752 : CollatzResearch.WordTrace tailWord_8009752 prefixEnd_8009752 4112852699311451042163827 := by
  unfold tailWord_8009752
  simp only [CollatzResearch.WordTrace]
  refine ⟨146069827839021967789055755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194759770452029290385407673 146069827839021967789055755)
  ·
    refine ⟨219104741758532951683583633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146069827839021967789055755 219104741758532951683583633)
    ·
      refine ⟨164328556318899713762687725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219104741758532951683583633 164328556318899713762687725)
      ·
        refine ⟨61623208619587392661007897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164328556318899713762687725 61623208619587392661007897)
        ·
          refine ⟨46217406464690544495755923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61623208619587392661007897 46217406464690544495755923)
          ·
            refine ⟨69326109697035816743633885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46217406464690544495755923 69326109697035816743633885)
            ·
              refine ⟨25997291136388431278862707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69326109697035816743633885 25997291136388431278862707)
              ·
                refine ⟨38995936704582646918294061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25997291136388431278862707 38995936704582646918294061)
                ·
                  refine ⟨14623476264218492594360273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38995936704582646918294061 14623476264218492594360273)
                  ·
                    refine ⟨10967607198163869445770205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14623476264218492594360273 10967607198163869445770205)
                    ·
                      refine ⟨4112852699311451042163827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10967607198163869445770205 4112852699311451042163827)
                      ·
                        rfl

theorem cell23_8009752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_8009752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009752 prefixEnd_8009752 := by exact prefixLift 8009752
  have htrace : WordTrace (prefixWord ++ tailWord_8009752) baseStart_8009752 baseEnd_8009752 := by
    simpa [prefixWord, tailWord_8009752, baseEnd_8009752] using wordTrace_append hprefix tailTrace_8009752
  have hstable : (prefixWord ++ tailWord_8009752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009752).length < 2 ^ (prefixWord ++ tailWord_8009752).sum := by decide
  have hdescent : baseEnd_8009752 < baseStart_8009752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009762 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_8009762 : Nat := 118140960795 + 8009762 * 2 ^ 59
def prefixEnd_8009762 : Nat := 4983230072969 + 3 ^ 40 * 8009762 * 2
def baseEnd_8009762 : Nat := 4112857834117996003038781

theorem tailTrace_8009762 : CollatzResearch.WordTrace tailWord_8009762 prefixEnd_8009762 4112857834117996003038781 := by
  unfold tailWord_8009762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73035005102001926821493885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194760013605338471523983693 73035005102001926821493885)
  ·
    refine ⟨27388126913250722558060207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73035005102001926821493885 27388126913250722558060207)
    ·
      refine ⟨41082190369876083837090311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27388126913250722558060207 41082190369876083837090311)
      ·
        refine ⟨61623285554814125755635467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41082190369876083837090311 61623285554814125755635467)
        ·
          refine ⟨92434928332221188633453201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61623285554814125755635467 92434928332221188633453201)
          ·
            refine ⟨69326196249165891475089901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92434928332221188633453201 69326196249165891475089901)
            ·
              refine ⟨25997323593437209303158713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69326196249165891475089901 25997323593437209303158713)
              ·
                refine ⟨19497992695077906977369035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25997323593437209303158713 19497992695077906977369035)
                ·
                  refine ⟨29246989042616860466053553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19497992695077906977369035 29246989042616860466053553)
                  ·
                    refine ⟨21935241781962645349540165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29246989042616860466053553 21935241781962645349540165)
                    ·
                      refine ⟨4112857834117996003038781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21935241781962645349540165 4112857834117996003038781)
                      ·
                        rfl

theorem cell23_8009762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_8009762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009762 prefixEnd_8009762 := by exact prefixLift 8009762
  have htrace : WordTrace (prefixWord ++ tailWord_8009762) baseStart_8009762 baseEnd_8009762 := by
    simpa [prefixWord, tailWord_8009762, baseEnd_8009762] using wordTrace_append hprefix tailTrace_8009762
  have hstable : (prefixWord ++ tailWord_8009762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009762).length < 2 ^ (prefixWord ++ tailWord_8009762).sum := by decide
  have hdescent : baseEnd_8009762 < baseStart_8009762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009783 : List Nat := [1, 1, 3, 1, 2, 2, 6, 2, 1, 2, 2]
def baseStart_8009783 : Nat := 118140960795 + 8009783 * 2 ^ 59
def prefixEnd_8009783 : Nat := 4983230072969 + 3 ^ 40 * 8009783 * 2
def baseEnd_8009783 : Nat := 4112868617211740420876185

theorem tailTrace_8009783 : CollatzResearch.WordTrace tailWord_8009783 prefixEnd_8009783 4112868617211740420876185 := by
  unfold tailWord_8009783
  simp only [CollatzResearch.WordTrace]
  refine ⟨292140786340931627872490003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194760524227287751914993335 292140786340931627872490003)
  ·
    refine ⟨438211179511397441808735005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292140786340931627872490003 438211179511397441808735005)
    ·
      refine ⟨164329192316774040678275627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438211179511397441808735005 164329192316774040678275627)
      ·
        refine ⟨246493788475161061017413441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164329192316774040678275627 246493788475161061017413441)
        ·
          refine ⟨184870341356370795763060081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246493788475161061017413441 184870341356370795763060081)
          ·
            refine ⟨138652756017278096822295061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184870341356370795763060081 138652756017278096822295061)
            ·
              refine ⟨6499347938309910788545081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138652756017278096822295061 6499347938309910788545081)
              ·
                refine ⟨4874510953732433091408811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6499347938309910788545081 4874510953732433091408811)
                ·
                  refine ⟨7311766430598649637113217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874510953732433091408811 7311766430598649637113217)
                  ·
                    refine ⟨5483824822948987227834913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7311766430598649637113217 5483824822948987227834913)
                    ·
                      refine ⟨4112868617211740420876185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483824822948987227834913 4112868617211740420876185)
                      ·
                        rfl

theorem cell23_8009783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_8009783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009783 prefixEnd_8009783 := by exact prefixLift 8009783
  have htrace : WordTrace (prefixWord ++ tailWord_8009783) baseStart_8009783 baseEnd_8009783 := by
    simpa [prefixWord, tailWord_8009783, baseEnd_8009783] using wordTrace_append hprefix tailTrace_8009783
  have hstable : (prefixWord ++ tailWord_8009783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009783).length < 2 ^ (prefixWord ++ tailWord_8009783).sum := by decide
  have hdescent : baseEnd_8009783 < baseStart_8009783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009799 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_8009799 : Nat := 118140960795 + 8009799 * 2 ^ 59
def prefixEnd_8009799 : Nat := 4983230072969 + 3 ^ 40 * 8009799 * 2
def baseEnd_8009799 : Nat := 4112876832902212358276111

theorem tailTrace_8009799 : CollatzResearch.WordTrace tailWord_8009799 prefixEnd_8009799 4112876832902212358276111 := by
  unfold tailWord_8009799
  simp only [CollatzResearch.WordTrace]
  refine ⟨292141369908873662605072451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194760913272582441736714967 292141369908873662605072451)
  ·
    refine ⟨438212054863310493907608677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292141369908873662605072451 438212054863310493907608677)
    ·
      refine ⟨82164760286870717607676627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438212054863310493907608677 82164760286870717607676627)
      ·
        refine ⟨123247140430306076411514941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82164760286870717607676627 123247140430306076411514941)
        ·
          refine ⟨46217677661364778654318103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123247140430306076411514941 46217677661364778654318103)
          ·
            refine ⟨69326516492047167981477155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46217677661364778654318103 69326516492047167981477155)
            ·
              refine ⟨103989774738070751972215733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69326516492047167981477155 103989774738070751972215733)
              ·
                refine ⟨9749041381694132997395225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103989774738070751972215733 9749041381694132997395225)
                ·
                  refine ⟨7311781036270599748046419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9749041381694132997395225 7311781036270599748046419)
                  ·
                    refine ⟨10967671554405899622069629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7311781036270599748046419 10967671554405899622069629)
                    ·
                      refine ⟨4112876832902212358276111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10967671554405899622069629 4112876832902212358276111)
                      ·
                        rfl

theorem cell23_8009799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_8009799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009799 prefixEnd_8009799 := by exact prefixLift 8009799
  have htrace : WordTrace (prefixWord ++ tailWord_8009799) baseStart_8009799 baseEnd_8009799 := by
    simpa [prefixWord, tailWord_8009799, baseEnd_8009799] using wordTrace_append hprefix tailTrace_8009799
  have hstable : (prefixWord ++ tailWord_8009799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009799).length < 2 ^ (prefixWord ++ tailWord_8009799).sum := by decide
  have hdescent : baseEnd_8009799 < baseStart_8009799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009809 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 1, 3, 2]
def baseStart_8009809 : Nat := 118140960795 + 8009809 * 2 ^ 59
def prefixEnd_8009809 : Nat := 4983230072969 + 3 ^ 40 * 8009809 * 2
def baseEnd_8009809 : Nat := 4112881967708757319151065

theorem tailTrace_8009809 : CollatzResearch.WordTrace tailWord_8009809 prefixEnd_8009809 4112881967708757319151065 := by
  unfold tailWord_8009809
  simp only [CollatzResearch.WordTrace]
  refine ⟨292141734638837434312936481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194761156425891622875290987 292141734638837434312936481)
  ·
    refine ⟨219106300979128075734702361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292141734638837434312936481 219106300979128075734702361)
    ·
      refine ⟨164329725734346056801026771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219106300979128075734702361 164329725734346056801026771)
      ·
        refine ⟨246494588601519085201540157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164329725734346056801026771 246494588601519085201540157)
        ·
          refine ⟨92435470725569656950577559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246494588601519085201540157 92435470725569656950577559)
          ·
            refine ⟨138653206088354485425866339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92435470725569656950577559 138653206088354485425866339)
            ·
              refine ⟨207979809132531728138799509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138653206088354485425866339 207979809132531728138799509)
              ·
                refine ⟨9749053553087424756506227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207979809132531728138799509 9749053553087424756506227)
                ·
                  refine ⟨14623580329631137134759341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9749053553087424756506227 14623580329631137134759341)
                  ·
                    refine ⟨5483842623611676425534753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14623580329631137134759341 5483842623611676425534753)
                    ·
                      refine ⟨4112881967708757319151065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5483842623611676425534753 4112881967708757319151065)
                      ·
                        rfl

theorem cell23_8009809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_8009809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009809 prefixEnd_8009809 := by exact prefixLift 8009809
  have htrace : WordTrace (prefixWord ++ tailWord_8009809) baseStart_8009809 baseEnd_8009809 := by
    simpa [prefixWord, tailWord_8009809, baseEnd_8009809] using wordTrace_append hprefix tailTrace_8009809
  have hstable : (prefixWord ++ tailWord_8009809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009809).length < 2 ^ (prefixWord ++ tailWord_8009809).sum := by decide
  have hdescent : baseEnd_8009809 < baseStart_8009809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009825 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_8009825 : Nat := 118140960795 + 8009825 * 2 ^ 59
def prefixEnd_8009825 : Nat := 4983230072969 + 3 ^ 40 * 8009825 * 2
def baseEnd_8009825 : Nat := 4112890183399229256550991

theorem tailTrace_8009825 : CollatzResearch.WordTrace tailWord_8009825 prefixEnd_8009825 4112890183399229256550991 := by
  unfold tailWord_8009825
  simp only [CollatzResearch.WordTrace]
  refine ⟨292142318206779469045518929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194761545471186312697012619 292142318206779469045518929)
  ·
    refine ⟨219106738655084601784139197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292142318206779469045518929 219106738655084601784139197)
    ·
      refine ⟨82165026995656725669052199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219106738655084601784139197 82165026995656725669052199)
      ·
        refine ⟨123247540493485088503578299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82165026995656725669052199 123247540493485088503578299)
        ·
          refine ⟨184871310740227632755367449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123247540493485088503578299 184871310740227632755367449)
          ·
            refine ⟨138653483055170724566525587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184871310740227632755367449 138653483055170724566525587)
            ·
              refine ⟨207980224582756086849788381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138653483055170724566525587 207980224582756086849788381)
              ·
                refine ⟨77992584218533532568670643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207980224582756086849788381 77992584218533532568670643)
                ·
                  refine ⟨116988876327800298853005965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77992584218533532568670643 116988876327800298853005965)
                  ·
                    refine ⟨43870828622925112069877237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116988876327800298853005965 43870828622925112069877237)
                    ·
                      refine ⟨4112890183399229256550991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43870828622925112069877237 4112890183399229256550991)
                      ·
                        rfl

theorem cell23_8009825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_8009825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009825 prefixEnd_8009825 := by exact prefixLift 8009825
  have htrace : WordTrace (prefixWord ++ tailWord_8009825) baseStart_8009825 baseEnd_8009825 := by
    simpa [prefixWord, tailWord_8009825, baseEnd_8009825] using wordTrace_append hprefix tailTrace_8009825
  have hstable : (prefixWord ++ tailWord_8009825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009825).length < 2 ^ (prefixWord ++ tailWord_8009825).sum := by decide
  have hdescent : baseEnd_8009825 < baseStart_8009825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009852 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_8009852 : Nat := 118140960795 + 8009852 * 2 ^ 59
def prefixEnd_8009852 : Nat := 4983230072969 + 3 ^ 40 * 8009852 * 2
def baseEnd_8009852 : Nat := 4112904047376900650913367

theorem tailTrace_8009852 : CollatzResearch.WordTrace tailWord_8009852 prefixEnd_8009852 4112904047376900650913367 := by
  unfold tailWord_8009852
  simp only [CollatzResearch.WordTrace]
  refine ⟨146071651488840826328375905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194762201985121101771167873 146071651488840826328375905)
  ·
    refine ⟨109553738616630619746281929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146071651488840826328375905 109553738616630619746281929)
    ·
      refine ⟨82165303962472964809711447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109553738616630619746281929 82165303962472964809711447)
      ·
        refine ⟨123247955943709447214567171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82165303962472964809711447 123247955943709447214567171)
        ·
          refine ⟨184871933915564170821850757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123247955943709447214567171 184871933915564170821850757)
          ·
            refine ⟨34663487609168282029097017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184871933915564170821850757 34663487609168282029097017)
            ·
              refine ⟨25997615706876211521822763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34663487609168282029097017 25997615706876211521822763)
              ·
                refine ⟨38996423560314317282734145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25997615706876211521822763 38996423560314317282734145)
                ·
                  refine ⟨29247317670235737962050609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38996423560314317282734145 29247317670235737962050609)
                  ·
                    refine ⟨21935488252676803471537957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29247317670235737962050609 21935488252676803471537957)
                    ·
                      refine ⟨4112904047376900650913367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21935488252676803471537957 4112904047376900650913367)
                      ·
                        rfl

theorem cell23_8009852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_8009852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009852 prefixEnd_8009852 := by exact prefixLift 8009852
  have htrace : WordTrace (prefixWord ++ tailWord_8009852) baseStart_8009852 baseEnd_8009852 := by
    simpa [prefixWord, tailWord_8009852, baseEnd_8009852] using wordTrace_append hprefix tailTrace_8009852
  have hstable : (prefixWord ++ tailWord_8009852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009852).length < 2 ^ (prefixWord ++ tailWord_8009852).sum := by decide
  have hdescent : baseEnd_8009852 < baseStart_8009852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009876 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_8009876 : Nat := 118140960795 + 8009876 * 2 ^ 59
def prefixEnd_8009876 : Nat := 4983230072969 + 3 ^ 40 * 8009876 * 2
def baseEnd_8009876 : Nat := 4112916370912608557013257

theorem tailTrace_8009876 : CollatzResearch.WordTrace tailWord_8009876 prefixEnd_8009876 4112916370912608557013257 := by
  unfold tailWord_8009876
  simp only [CollatzResearch.WordTrace]
  refine ⟨146072089164797352377812741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194762785553063136503750321 146072089164797352377812741)
  ·
    refine ⟨27388516718399503570839889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146072089164797352377812741 27388516718399503570839889)
    ·
      refine ⟨20541387538799627678129917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27388516718399503570839889 20541387538799627678129917)
      ·
        refine ⟨7703020327049860379298719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20541387538799627678129917 7703020327049860379298719)
        ·
          refine ⟨11554530490574790568948079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703020327049860379298719 11554530490574790568948079)
          ·
            refine ⟨17331795735862185853422119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11554530490574790568948079 17331795735862185853422119)
            ·
              refine ⟨25997693603793278780133179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17331795735862185853422119 25997693603793278780133179)
              ·
                refine ⟨38996540405689918170199769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25997693603793278780133179 38996540405689918170199769)
                ·
                  refine ⟨29247405304267438627649827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38996540405689918170199769 29247405304267438627649827)
                  ·
                    refine ⟨43871107956401157941474741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29247405304267438627649827 43871107956401157941474741)
                    ·
                      refine ⟨4112916370912608557013257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43871107956401157941474741 4112916370912608557013257)
                      ·
                        rfl

theorem cell23_8009876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_8009876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009876 prefixEnd_8009876 := by exact prefixLift 8009876
  have htrace : WordTrace (prefixWord ++ tailWord_8009876) baseStart_8009876 baseEnd_8009876 := by
    simpa [prefixWord, tailWord_8009876, baseEnd_8009876] using wordTrace_append hprefix tailTrace_8009876
  have hstable : (prefixWord ++ tailWord_8009876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009876).length < 2 ^ (prefixWord ++ tailWord_8009876).sum := by decide
  have hdescent : baseEnd_8009876 < baseStart_8009876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8009912 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_8009912 : Nat := 118140960795 + 8009912 * 2 ^ 59
def prefixEnd_8009912 : Nat := 4983230072969 + 3 ^ 40 * 8009912 * 2
def baseEnd_8009912 : Nat := 4112934856216170416163091

theorem tailTrace_8009912 : CollatzResearch.WordTrace tailWord_8009912 prefixEnd_8009912 4112934856216170416163091 := by
  unfold tailWord_8009912
  simp only [CollatzResearch.WordTrace]
  refine ⟨146072745678732141451967995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194763660904976188602623993 146072745678732141451967995)
  ·
    refine ⟨219109118518098212177951993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146072745678732141451967995 219109118518098212177951993)
    ·
      refine ⟨164331838888573659133463995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219109118518098212177951993 164331838888573659133463995)
      ·
        refine ⟨246497758332860488700195993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164331838888573659133463995 246497758332860488700195993)
        ·
          refine ⟨184873318749645366525146995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246497758332860488700195993 184873318749645366525146995)
          ·
            refine ⟨277309978124468049787720493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184873318749645366525146995 277309978124468049787720493)
            ·
              refine ⟨103991241796675518670395185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277309978124468049787720493 103991241796675518670395185)
              ·
                refine ⟨77993431347506639002796389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103991241796675518670395185 77993431347506639002796389)
                ·
                  refine ⟨14623768377657494813024323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77993431347506639002796389 14623768377657494813024323)
                  ·
                    refine ⟨21935652566486242219536485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14623768377657494813024323 21935652566486242219536485)
                    ·
                      refine ⟨4112934856216170416163091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21935652566486242219536485 4112934856216170416163091)
                      ·
                        rfl

theorem cell23_8009912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_8009912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8009912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8009912 prefixEnd_8009912 := by exact prefixLift 8009912
  have htrace : WordTrace (prefixWord ++ tailWord_8009912) baseStart_8009912 baseEnd_8009912 := by
    simpa [prefixWord, tailWord_8009912, baseEnd_8009912] using wordTrace_append hprefix tailTrace_8009912
  have hstable : (prefixWord ++ tailWord_8009912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8009912).length < 2 ^ (prefixWord ++ tailWord_8009912).sum := by decide
  have hdescent : baseEnd_8009912 < baseStart_8009912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8009912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010039 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_8010039 : Nat := 118140960795 + 8010039 * 2 ^ 59
def prefixEnd_8010039 : Nat := 4983230072969 + 3 ^ 40 * 8010039 * 2
def baseEnd_8010039 : Nat := 4113000068259291419275007

theorem tailTrace_8010039 : CollatzResearch.WordTrace tailWord_8010039 prefixEnd_8010039 4113000068259291419275007 := by
  unfold tailWord_8010039
  simp only [CollatzResearch.WordTrace]
  refine ⟨292150123428004183593809171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194766748952002789062539447 292150123428004183593809171)
  ·
    refine ⟨438225185142006275390713757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292150123428004183593809171 438225185142006275390713757)
    ·
      refine ⟨164334444428252353271517659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 438225185142006275390713757 164334444428252353271517659)
      ·
        refine ⟨246501666642378529907276489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164334444428252353271517659 246501666642378529907276489)
        ·
          refine ⟨184876249981783897430457367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246501666642378529907276489 184876249981783897430457367)
          ·
            refine ⟨277314374972675846145686051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184876249981783897430457367 277314374972675846145686051)
            ·
              refine ⟨415971562459013769218529077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277314374972675846145686051 415971562459013769218529077)
              ·
                refine ⟨38997333980532540864237101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 415971562459013769218529077 38997333980532540864237101)
                ·
                  refine ⟨14624000242699702824088913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38997333980532540864237101 14624000242699702824088913)
                  ·
                    refine ⟨10968000182024777118066685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14624000242699702824088913 10968000182024777118066685)
                    ·
                      refine ⟨4113000068259291419275007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10968000182024777118066685 4113000068259291419275007)
                      ·
                        rfl

theorem cell23_8010039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_8010039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010039 prefixEnd_8010039 := by exact prefixLift 8010039
  have htrace : WordTrace (prefixWord ++ tailWord_8010039) baseStart_8010039 baseEnd_8010039 := by
    simpa [prefixWord, tailWord_8010039, baseEnd_8010039] using wordTrace_append hprefix tailTrace_8010039
  have hstable : (prefixWord ++ tailWord_8010039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010039).length < 2 ^ (prefixWord ++ tailWord_8010039).sum := by decide
  have hdescent : baseEnd_8010039 < baseStart_8010039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010046 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_8010046 : Nat := 118140960795 + 8010046 * 2 ^ 59
def prefixEnd_8010046 : Nat := 4983230072969 + 3 ^ 40 * 8010046 * 2
def baseEnd_8010046 : Nat := 1371001220874624297295825

theorem tailTrace_8010046 : CollatzResearch.WordTrace tailWord_8010046 prefixEnd_8010046 1371001220874624297295825 := by
  unfold tailWord_8010046
  simp only [CollatzResearch.WordTrace]
  refine ⟨36518797342372352973664249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194766919159319215859542661 36518797342372352973664249)
  ·
    refine ⟨27389098006779264730248187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36518797342372352973664249 27389098006779264730248187)
    ·
      refine ⟨41083647010168897095372281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27389098006779264730248187 41083647010168897095372281)
      ·
        refine ⟨30812735257626672821529211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41083647010168897095372281 30812735257626672821529211)
        ·
          refine ⟨46219102886440009232293817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30812735257626672821529211 46219102886440009232293817)
          ·
            refine ⟨34664327164830006924220363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46219102886440009232293817 34664327164830006924220363)
            ·
              refine ⟨51996490747245010386330545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34664327164830006924220363 51996490747245010386330545)
              ·
                refine ⟨38997368060433757789747909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51996490747245010386330545 38997368060433757789747909)
                ·
                  refine ⟨7312006511331329585577733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38997368060433757789747909 7312006511331329585577733)
                  ·
                    refine ⟨1371001220874624297295825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7312006511331329585577733 1371001220874624297295825)
                    ·
                      rfl

theorem cell23_8010046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_8010046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010046 prefixEnd_8010046 := by exact prefixLift 8010046
  have htrace : WordTrace (prefixWord ++ tailWord_8010046) baseStart_8010046 baseEnd_8010046 := by
    simpa [prefixWord, tailWord_8010046, baseEnd_8010046] using wordTrace_append hprefix tailTrace_8010046
  have hstable : (prefixWord ++ tailWord_8010046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010046).length < 2 ^ (prefixWord ++ tailWord_8010046).sum := by decide
  have hdescent : baseEnd_8010046 < baseStart_8010046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010056 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_8010056 : Nat := 118140960795 + 8010056 * 2 ^ 59
def prefixEnd_8010056 : Nat := 4983230072969 + 3 ^ 40 * 8010056 * 2
def baseEnd_8010056 : Nat := 4113008797430417852762429

theorem tailTrace_8010056 : CollatzResearch.WordTrace tailWord_8010056 prefixEnd_8010056 4113008797430417852762429 := by
  unfold tailWord_8010056
  simp only [CollatzResearch.WordTrace]
  refine ⟨146075371734471297748589011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194767162312628396998118681 146075371734471297748589011)
  ·
    refine ⟨219113057601706946622883517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146075371734471297748589011 219113057601706946622883517)
    ·
      refine ⟨82167396600640104983581319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219113057601706946622883517 82167396600640104983581319)
      ·
        refine ⟨123251094900960157475371979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82167396600640104983581319 123251094900960157475371979)
        ·
          refine ⟨184876642351440236213057969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123251094900960157475371979 184876642351440236213057969)
          ·
            refine ⟨138657481763580177159793477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184876642351440236213057969 138657481763580177159793477)
            ·
              refine ⟨25998277830671283217461277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138657481763580177159793477 25998277830671283217461277)
              ·
                refine ⟨9749354186501731206547979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25998277830671283217461277 9749354186501731206547979)
                ·
                  refine ⟨14624031279752596809821969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9749354186501731206547979 14624031279752596809821969)
                  ·
                    refine ⟨10968023459814447607366477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14624031279752596809821969 10968023459814447607366477)
                    ·
                      refine ⟨4113008797430417852762429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10968023459814447607366477 4113008797430417852762429)
                      ·
                        rfl

theorem cell23_8010056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_8010056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010056 prefixEnd_8010056 := by exact prefixLift 8010056
  have htrace : WordTrace (prefixWord ++ tailWord_8010056) baseStart_8010056 baseEnd_8010056 := by
    simpa [prefixWord, tailWord_8010056, baseEnd_8010056] using wordTrace_append hprefix tailTrace_8010056
  have hstable : (prefixWord ++ tailWord_8010056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010056).length < 2 ^ (prefixWord ++ tailWord_8010056).sum := by decide
  have hdescent : baseEnd_8010056 < baseStart_8010056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010080 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 2, 4]
def baseStart_8010080 : Nat := 118140960795 + 8010080 * 2 ^ 59
def prefixEnd_8010080 : Nat := 4983230072969 + 3 ^ 40 * 8010080 * 2
def baseEnd_8010080 : Nat := 1371007040322041919620773

theorem tailTrace_8010080 : CollatzResearch.WordTrace tailWord_8010080 prefixEnd_8010080 1371007040322041919620773 := by
  unfold tailWord_8010080
  simp only [CollatzResearch.WordTrace]
  refine ⟨146075809410427823798025847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194767745880570431730701129 146075809410427823798025847)
  ·
    refine ⟨219113714115641735697038771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146075809410427823798025847 219113714115641735697038771)
    ·
      refine ⟨328670571173462603545558157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219113714115641735697038771 328670571173462603545558157)
      ·
        refine ⟨123251464190048476329584309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328670571173462603545558157 123251464190048476329584309)
        ·
          refine ⟨11554824767817044655898529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123251464190048476329584309 11554824767817044655898529)
          ·
            refine ⟨8666118575862783491923897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11554824767817044655898529 8666118575862783491923897)
            ·
              refine ⟨6499588931897087618942923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8666118575862783491923897 6499588931897087618942923)
              ·
                refine ⟨9749383397845631428414385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499588931897087618942923 9749383397845631428414385)
                ·
                  refine ⟨7312037548384223571310789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9749383397845631428414385 7312037548384223571310789)
                  ·
                    refine ⟨1371007040322041919620773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7312037548384223571310789 1371007040322041919620773)
                    ·
                      rfl

theorem cell23_8010080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 4].length) (baseStart_8010080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010080 prefixEnd_8010080 := by exact prefixLift 8010080
  have htrace : WordTrace (prefixWord ++ tailWord_8010080) baseStart_8010080 baseEnd_8010080 := by
    simpa [prefixWord, tailWord_8010080, baseEnd_8010080] using wordTrace_append hprefix tailTrace_8010080
  have hstable : (prefixWord ++ tailWord_8010080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010080).length < 2 ^ (prefixWord ++ tailWord_8010080).sum := by decide
  have hdescent : baseEnd_8010080 < baseStart_8010080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010090 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_8010090 : Nat := 118140960795 + 8010090 * 2 ^ 59
def prefixEnd_8010090 : Nat := 4983230072969 + 3 ^ 40 * 8010090 * 2
def baseEnd_8010090 : Nat := 4113026255772670719737273

theorem tailTrace_8010090 : CollatzResearch.WordTrace tailWord_8010090 prefixEnd_8010090 4113026255772670719737273 := by
  unfold tailWord_8010090
  simp only [CollatzResearch.WordTrace]
  refine ⟨73037995887704854825978931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194767989033879612869277149 73037995887704854825978931)
  ·
    refine ⟨109556993831557282238968397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73037995887704854825978931 109556993831557282238968397)
    ·
      refine ⟨41083872686833980839613149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109556993831557282238968397 41083872686833980839613149)
      ·
        refine ⟨15406452257562742814854931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41083872686833980839613149 15406452257562742814854931)
        ·
          refine ⟨23109678386344114222282397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15406452257562742814854931 23109678386344114222282397)
          ·
            refine ⟨8666129394879042833355899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23109678386344114222282397 8666129394879042833355899)
            ·
              refine ⟨12999194092318564250033849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8666129394879042833355899 12999194092318564250033849)
              ·
                refine ⟨9749395569238923187525387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12999194092318564250033849 9749395569238923187525387)
                ·
                  refine ⟨14624093353858384781288081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9749395569238923187525387 14624093353858384781288081)
                  ·
                    refine ⟨10968070015393788585966061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14624093353858384781288081 10968070015393788585966061)
                    ·
                      refine ⟨4113026255772670719737273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10968070015393788585966061 4113026255772670719737273)
                      ·
                        rfl

theorem cell23_8010090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_8010090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010090 prefixEnd_8010090 := by exact prefixLift 8010090
  have htrace : WordTrace (prefixWord ++ tailWord_8010090) baseStart_8010090 baseEnd_8010090 := by
    simpa [prefixWord, tailWord_8010090, baseEnd_8010090] using wordTrace_append hprefix tailTrace_8010090
  have hstable : (prefixWord ++ tailWord_8010090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010090).length < 2 ^ (prefixWord ++ tailWord_8010090).sum := by decide
  have hdescent : baseEnd_8010090 < baseStart_8010090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010119 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 2, 6]
def baseStart_8010119 : Nat := 118140960795 + 8010119 * 2 ^ 59
def prefixEnd_8010119 : Nat := 4983230072969 + 3 ^ 40 * 8010119 * 2
def baseEnd_8010119 : Nat := 1371013715570550368758213

theorem tailTrace_8010119 : CollatzResearch.WordTrace tailWord_8010119 prefixEnd_8010119 1371013715570550368758213 := by
  unfold tailWord_8010119
  simp only [CollatzResearch.WordTrace]
  refine ⟨292153041267714357256721411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194768694178476238171147607 292153041267714357256721411)
  ·
    refine ⟨438229561901571535885082117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292153041267714357256721411 438229561901571535885082117)
    ·
      refine ⟨82168042856544662978452897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 438229561901571535885082117 82168042856544662978452897)
      ·
        refine ⟨61626032142408497233839673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82168042856544662978452897 61626032142408497233839673)
        ·
          refine ⟨46219524106806372925379755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61626032142408497233839673 46219524106806372925379755)
          ·
            refine ⟨69329286160209559388069633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46219524106806372925379755 69329286160209559388069633)
            ·
              refine ⟨51996964620157169541052225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69329286160209559388069633 51996964620157169541052225)
              ·
                refine ⟨38997723465117877155789169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51996964620157169541052225 38997723465117877155789169)
                ·
                  refine ⟨29248292598838407866841877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38997723465117877155789169 29248292598838407866841877)
                  ·
                    refine ⟨1371013715570550368758213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29248292598838407866841877 1371013715570550368758213)
                    ·
                      rfl

theorem cell23_8010119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_8010119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010119 prefixEnd_8010119 := by exact prefixLift 8010119
  have htrace : WordTrace (prefixWord ++ tailWord_8010119) baseStart_8010119 baseEnd_8010119 := by
    simpa [prefixWord, tailWord_8010119, baseEnd_8010119] using wordTrace_append hprefix tailTrace_8010119
  have hstable : (prefixWord ++ tailWord_8010119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010119).length < 2 ^ (prefixWord ++ tailWord_8010119).sum := by decide
  have hdescent : baseEnd_8010119 < baseStart_8010119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010126 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_8010126 : Nat := 118140960795 + 8010126 * 2 ^ 59
def prefixEnd_8010126 : Nat := 4983230072969 + 3 ^ 40 * 8010126 * 2
def baseEnd_8010126 : Nat := 4113044741076232578887107

theorem tailTrace_8010126 : CollatzResearch.WordTrace tailWord_8010126 prefixEnd_8010126 4113044741076232578887107 := by
  unfold tailWord_8010126
  simp only [CollatzResearch.WordTrace]
  refine ⟨36519162072336124681528279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194768864385792664968150821 36519162072336124681528279)
  ·
    refine ⟨54778743108504187022292419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36519162072336124681528279 54778743108504187022292419)
    ·
      refine ⟨82168114662756280533438629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54778743108504187022292419 82168114662756280533438629)
      ·
        refine ⟨15406521499266802600019743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82168114662756280533438629 15406521499266802600019743)
        ·
          refine ⟨23109782248900203900029615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15406521499266802600019743 23109782248900203900029615)
          ·
            refine ⟨34664673373350305850044423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23109782248900203900029615 34664673373350305850044423)
            ·
              refine ⟨51997010060025458775066635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34664673373350305850044423 51997010060025458775066635)
              ·
                refine ⟨77995515090038188162599953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51997010060025458775066635 77995515090038188162599953)
                ·
                  refine ⟨58496636317528641121949965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77995515090038188162599953 58496636317528641121949965)
                  ·
                    refine ⟨21936238619073240420731237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58496636317528641121949965 21936238619073240420731237)
                    ·
                      refine ⟨4113044741076232578887107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21936238619073240420731237 4113044741076232578887107)
                      ·
                        rfl

theorem cell23_8010126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_8010126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010126 prefixEnd_8010126 := by exact prefixLift 8010126
  have htrace : WordTrace (prefixWord ++ tailWord_8010126) baseStart_8010126 baseEnd_8010126 := by
    simpa [prefixWord, tailWord_8010126, baseEnd_8010126] using wordTrace_append hprefix tailTrace_8010126
  have hstable : (prefixWord ++ tailWord_8010126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010126).length < 2 ^ (prefixWord ++ tailWord_8010126).sum := by decide
  have hdescent : baseEnd_8010126 < baseStart_8010126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010136 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 2, 6]
def baseStart_8010136 : Nat := 118140960795 + 8010136 * 2 ^ 59
def prefixEnd_8010136 : Nat := 4983230072969 + 3 ^ 40 * 8010136 * 2
def baseEnd_8010136 : Nat := 1371016625294259179920687

theorem tailTrace_8010136 : CollatzResearch.WordTrace tailWord_8010136 prefixEnd_8010136 1371016625294259179920687 := by
  unfold tailWord_8010136
  simp only [CollatzResearch.WordTrace]
  refine ⟨146076830654326384580045131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194769107539101846106726841 146076830654326384580045131)
  ·
    refine ⟨219115245981489576870067697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146076830654326384580045131 219115245981489576870067697)
    ·
      refine ⟨164336434486117182652550773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219115245981489576870067697 164336434486117182652550773)
      ·
        refine ⟨15406540733073485873676635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164336434486117182652550773 15406540733073485873676635)
        ·
          refine ⟨23109811099610228810514953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15406540733073485873676635 23109811099610228810514953)
          ·
            refine ⟨17332358324707671607886215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23109811099610228810514953 17332358324707671607886215)
            ·
              refine ⟨25998537487061507411829323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17332358324707671607886215 25998537487061507411829323)
              ·
                refine ⟨38997806230592261117743985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25998537487061507411829323 38997806230592261117743985)
                ·
                  refine ⟨29248354672944195838307989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38997806230592261117743985 29248354672944195838307989)
                  ·
                    refine ⟨1371016625294259179920687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29248354672944195838307989 1371016625294259179920687)
                    ·
                      rfl

theorem cell23_8010136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_8010136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010136 prefixEnd_8010136 := by exact prefixLift 8010136
  have htrace : WordTrace (prefixWord ++ tailWord_8010136) baseStart_8010136 baseEnd_8010136 := by
    simpa [prefixWord, tailWord_8010136, baseEnd_8010136] using wordTrace_append hprefix tailTrace_8010136
  have hstable : (prefixWord ++ tailWord_8010136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010136).length < 2 ^ (prefixWord ++ tailWord_8010136).sum := by decide
  have hdescent : baseEnd_8010136 < baseStart_8010136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010143 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 1, 4, 2]
def baseStart_8010143 : Nat := 118140960795 + 8010143 * 2 ^ 59
def prefixEnd_8010143 : Nat := 4983230072969 + 3 ^ 40 * 8010143 * 2
def baseEnd_8010143 : Nat := 4113053470247359012374529

theorem tailTrace_8010143 : CollatzResearch.WordTrace tailWord_8010143 prefixEnd_8010143 4113053470247359012374529 := by
  unfold tailWord_8010143
  simp only [CollatzResearch.WordTrace]
  refine ⟨292153916619627409355595083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194769277746418272903730055 292153916619627409355595083)
  ·
    refine ⟨438230874929441114033392625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292153916619627409355595083 438230874929441114033392625)
    ·
      refine ⟨328673156197080835525044469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438230874929441114033392625 328673156197080835525044469)
      ·
        refine ⟨30813108393476328330472919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328673156197080835525044469 30813108393476328330472919)
        ·
          refine ⟨46219662590214492495709379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30813108393476328330472919 46219662590214492495709379)
          ·
            refine ⟨69329493885321738743564069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46219662590214492495709379 69329493885321738743564069)
            ·
              refine ⟨12999280103497826014418263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69329493885321738743564069 12999280103497826014418263)
              ·
                refine ⟨19498920155246739021627395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12999280103497826014418263 19498920155246739021627395)
                ·
                  refine ⟨29248380232870108532441093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19498920155246739021627395 29248380232870108532441093)
                  ·
                    refine ⟨5484071293663145349832705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29248380232870108532441093 5484071293663145349832705)
                    ·
                      refine ⟨4113053470247359012374529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5484071293663145349832705 4113053470247359012374529)
                      ·
                        rfl

theorem cell23_8010143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_8010143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010143 prefixEnd_8010143 := by exact prefixLift 8010143
  have htrace : WordTrace (prefixWord ++ tailWord_8010143) baseStart_8010143 baseEnd_8010143 := by
    simpa [prefixWord, tailWord_8010143, baseEnd_8010143] using wordTrace_append hprefix tailTrace_8010143
  have hstable : (prefixWord ++ tailWord_8010143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010143).length < 2 ^ (prefixWord ++ tailWord_8010143).sum := by decide
  have hdescent : baseEnd_8010143 < baseStart_8010143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010146 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_8010146 : Nat := 118140960795 + 8010146 * 2 ^ 59
def prefixEnd_8010146 : Nat := 4983230072969 + 3 ^ 40 * 8010146 * 2
def baseEnd_8010146 : Nat := 4113055010689322500637015

theorem tailTrace_8010146 : CollatzResearch.WordTrace tailWord_8010146 prefixEnd_8010146 4113055010689322500637015 := by
  unfold tailWord_8010146
  simp only [CollatzResearch.WordTrace]
  refine ⟨73038506509654135216988573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194769350692411027245302861 73038506509654135216988573)
  ·
    refine ⟨27389439941120300706370715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73038506509654135216988573 27389439941120300706370715)
    ·
      refine ⟨41084159911680451059556073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27389439941120300706370715 41084159911680451059556073)
      ·
        refine ⟨30813119933760338294667055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41084159911680451059556073 30813119933760338294667055)
        ·
          refine ⟨46219679900640507442000583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30813119933760338294667055 46219679900640507442000583)
          ·
            refine ⟨69329519850960761163000875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46219679900640507442000583 69329519850960761163000875)
            ·
              refine ⟨103994279776441141744501313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69329519850960761163000875 103994279776441141744501313)
              ·
                refine ⟨77995709832330856308375985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103994279776441141744501313 77995709832330856308375985)
                ·
                  refine ⟨58496782374248142231281989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77995709832330856308375985 58496782374248142231281989)
                  ·
                    refine ⟨10968146695171526668365373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58496782374248142231281989 10968146695171526668365373)
                    ·
                      refine ⟨4113055010689322500637015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10968146695171526668365373 4113055010689322500637015)
                      ·
                        rfl

theorem cell23_8010146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_8010146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010146 prefixEnd_8010146 := by exact prefixLift 8010146
  have htrace : WordTrace (prefixWord ++ tailWord_8010146) baseStart_8010146 baseEnd_8010146 := by
    simpa [prefixWord, tailWord_8010146, baseEnd_8010146] using wordTrace_append hprefix tailTrace_8010146
  have hstable : (prefixWord ++ tailWord_8010146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010146).length < 2 ^ (prefixWord ++ tailWord_8010146).sum := by decide
  have hdescent : baseEnd_8010146 < baseStart_8010146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010149 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 7]
def baseStart_8010149 : Nat := 118140960795 + 8010149 * 2 ^ 59
def prefixEnd_8010149 : Nat := 4983230072969 + 3 ^ 40 * 8010149 * 2
def baseEnd_8010149 : Nat := 457006283459031776544389

theorem tailTrace_8010149 : CollatzResearch.WordTrace tailWord_8010149 prefixEnd_8010149 457006283459031776544389 := by
  unfold tailWord_8010149
  simp only [CollatzResearch.WordTrace]
  refine ⟨292154135457605672380313501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194769423638403781586875667 292154135457605672380313501)
  ·
    refine ⟨109557800796602127142617563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292154135457605672380313501 109557800796602127142617563)
    ·
      refine ⟨164336701194903190713926345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109557800796602127142617563 164336701194903190713926345)
      ·
        refine ⟨123252525896177393035444759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164336701194903190713926345 123252525896177393035444759)
        ·
          refine ⟨184878788844266089553167139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123252525896177393035444759 184878788844266089553167139)
          ·
            refine ⟨277318183266399134329750709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184878788844266089553167139 277318183266399134329750709)
            ·
              refine ⟨25998579681224918843414129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277318183266399134329750709 25998579681224918843414129)
              ·
                refine ⟨19498934760918689132560597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25998579681224918843414129 19498934760918689132560597)
                ·
                  refine ⟨457006283459031776544389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19498934760918689132560597 457006283459031776544389)
                  ·
                    rfl

theorem cell23_8010149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_8010149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010149 prefixEnd_8010149 := by exact prefixLift 8010149
  have htrace : WordTrace (prefixWord ++ tailWord_8010149) baseStart_8010149 baseEnd_8010149 := by
    simpa [prefixWord, tailWord_8010149, baseEnd_8010149] using wordTrace_append hprefix tailTrace_8010149
  have hstable : (prefixWord ++ tailWord_8010149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010149).length < 2 ^ (prefixWord ++ tailWord_8010149).sum := by decide
  have hdescent : baseEnd_8010149 < baseStart_8010149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010164 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_8010164 : Nat := 118140960795 + 8010164 * 2 ^ 59
def prefixEnd_8010164 : Nat := 4983230072969 + 3 ^ 40 * 8010164 * 2
def baseEnd_8010164 : Nat := 4113064253341103430211933

theorem tailTrace_8010164 : CollatzResearch.WordTrace tailWord_8010164 prefixEnd_8010164 4113064253341103430211933 := by
  unfold tailWord_8010164
  simp only [CollatzResearch.WordTrace]
  refine ⟨146077341276275664971054773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194769788368367553294739697 146077341276275664971054773)
  ·
    refine ⟨13694750744650843591036385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146077341276275664971054773 13694750744650843591036385)
    ·
      refine ⟨10271063058488132693277289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13694750744650843591036385 10271063058488132693277289)
      ·
        refine ⟨7703297293866099519957967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10271063058488132693277289 7703297293866099519957967)
        ·
          refine ⟨11554945940799149279936951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703297293866099519957967 11554945940799149279936951)
          ·
            refine ⟨17332418911198723919905427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11554945940799149279936951 17332418911198723919905427)
            ·
              refine ⟨25998628366798085879858141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17332418911198723919905427 25998628366798085879858141)
              ·
                refine ⟨9749485637549282204946803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25998628366798085879858141 9749485637549282204946803)
                ·
                  refine ⟨14624228456323923307420205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9749485637549282204946803 14624228456323923307420205)
                  ·
                    refine ⟨5484085671121471240282577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14624228456323923307420205 5484085671121471240282577)
                    ·
                      refine ⟨4113064253341103430211933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5484085671121471240282577 4113064253341103430211933)
                      ·
                        rfl

theorem cell23_8010164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_8010164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010164 prefixEnd_8010164 := by exact prefixLift 8010164
  have htrace : WordTrace (prefixWord ++ tailWord_8010164) baseStart_8010164 baseEnd_8010164 := by
    simpa [prefixWord, tailWord_8010164, baseEnd_8010164] using wordTrace_append hprefix tailTrace_8010164
  have hstable : (prefixWord ++ tailWord_8010164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010164).length < 2 ^ (prefixWord ++ tailWord_8010164).sum := by decide
  have hdescent : baseEnd_8010164 < baseStart_8010164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010179 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 4, 5]
def baseStart_8010179 : Nat := 118140960795 + 8010179 * 2 ^ 59
def prefixEnd_8010179 : Nat := 4983230072969 + 3 ^ 40 * 8010179 * 2
def baseEnd_8010179 : Nat := 1371023985183640290508121

theorem tailTrace_8010179 : CollatzResearch.WordTrace tailWord_8010179 prefixEnd_8010179 1371023985183640290508121 := by
  unfold tailWord_8010179
  simp only [CollatzResearch.WordTrace]
  refine ⟨292155229647496987503905591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194770153098331325002603727 292155229647496987503905591)
  ·
    refine ⟨438232844471245481255858387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292155229647496987503905591 438232844471245481255858387)
    ·
      refine ⟨657349266706868221883787581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438232844471245481255858387 657349266706868221883787581)
      ·
        refine ⟨246505975015075583206420343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 657349266706868221883787581 246505975015075583206420343)
        ·
          refine ⟨369758962522613374809630515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246505975015075583206420343 369758962522613374809630515)
          ·
            refine ⟨554638443783920062214445773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369758962522613374809630515 554638443783920062214445773)
            ·
              refine ⟨207989416418970023330417165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554638443783920062214445773 207989416418970023330417165)
              ·
                refine ⟨77996031157113758748906437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207989416418970023330417165 77996031157113758748906437)
                ·
                  refine ⟨14624255841958829765419957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77996031157113758748906437 14624255841958829765419957)
                  ·
                    refine ⟨1371023985183640290508121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14624255841958829765419957 1371023985183640290508121)
                    ·
                      rfl

theorem cell23_8010179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 5].length) (baseStart_8010179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010179 prefixEnd_8010179 := by exact prefixLift 8010179
  have htrace : WordTrace (prefixWord ++ tailWord_8010179) baseStart_8010179 baseEnd_8010179 := by
    simpa [prefixWord, tailWord_8010179, baseEnd_8010179] using wordTrace_append hprefix tailTrace_8010179
  have hstable : (prefixWord ++ tailWord_8010179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010179).length < 2 ^ (prefixWord ++ tailWord_8010179).sum := by decide
  have hdescent : baseEnd_8010179 < baseStart_8010179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010194 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_8010194 : Nat := 118140960795 + 8010194 * 2 ^ 59
def prefixEnd_8010194 : Nat := 4983230072969 + 3 ^ 40 * 8010194 * 2
def baseEnd_8010194 : Nat := 4113079657760738312836795

theorem tailTrace_8010194 : CollatzResearch.WordTrace tailWord_8010194 prefixEnd_8010194 4113079657760738312836795 := by
  unfold tailWord_8010194
  simp only [CollatzResearch.WordTrace]
  refine ⟨73038944185610661266425409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194770517828295096710467757 73038944185610661266425409)
  ·
    refine ⟨54779208139207995949819057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73038944185610661266425409 54779208139207995949819057)
    ·
      refine ⟨41084406104405996962364293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54779208139207995949819057 41084406104405996962364293)
      ·
        refine ⟨7703326144576124430443305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41084406104405996962364293 7703326144576124430443305)
        ·
          refine ⟨5777494608432093322832479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7703326144576124430443305 5777494608432093322832479)
          ·
            refine ⟨8666241912648139984248719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777494608432093322832479 8666241912648139984248719)
            ·
              refine ⟨12999362868972209976373079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8666241912648139984248719 12999362868972209976373079)
              ·
                refine ⟨19499044303458314964559619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12999362868972209976373079 19499044303458314964559619)
                ·
                  refine ⟨29248566455187472446839429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19499044303458314964559619 29248566455187472446839429)
                  ·
                    refine ⟨5484106210347651083782393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29248566455187472446839429 5484106210347651083782393)
                    ·
                      refine ⟨4113079657760738312836795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5484106210347651083782393 4113079657760738312836795)
                      ·
                        rfl

theorem cell23_8010194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_8010194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010194 prefixEnd_8010194 := by exact prefixLift 8010194
  have htrace : WordTrace (prefixWord ++ tailWord_8010194) baseStart_8010194 baseEnd_8010194 := by
    simpa [prefixWord, tailWord_8010194, baseEnd_8010194] using wordTrace_append hprefix tailTrace_8010194
  have hstable : (prefixWord ++ tailWord_8010194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010194).length < 2 ^ (prefixWord ++ tailWord_8010194).sum := by decide
  have hdescent : baseEnd_8010194 < baseStart_8010194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010196 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_8010196 : Nat := 118140960795 + 8010196 * 2 ^ 59
def prefixEnd_8010196 : Nat := 4983230072969 + 3 ^ 40 * 8010196 * 2
def baseEnd_8010196 : Nat := 1371026894907349101670595

theorem tailTrace_8010196 : CollatzResearch.WordTrace tailWord_8010196 prefixEnd_8010196 1371026894907349101670595 := by
  unfold tailWord_8010196
  simp only [CollatzResearch.WordTrace]
  refine ⟨146077924844217699703637221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194770566458956932938182961 146077924844217699703637221)
  ·
    refine ⟨27389610908290818694431979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146077924844217699703637221 27389610908290818694431979)
    ·
      refine ⟨41084416362436228041647969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27389610908290818694431979 41084416362436228041647969)
      ·
        refine ⟨30813312271827171031235977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41084416362436228041647969 30813312271827171031235977)
        ·
          refine ⟨23109984203870378273426983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30813312271827171031235977 23109984203870378273426983)
          ·
            refine ⟨34664976305805567410140475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23109984203870378273426983 34664976305805567410140475)
            ·
              refine ⟨51997464458708351115210713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34664976305805567410140475 51997464458708351115210713)
              ·
                refine ⟨38998098344031263336408035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51997464458708351115210713 38998098344031263336408035)
                ·
                  refine ⟨58497147516046895004612053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38998098344031263336408035 58497147516046895004612053)
                  ·
                    refine ⟨1371026894907349101670595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58497147516046895004612053 1371026894907349101670595)
                    ·
                      rfl

theorem cell23_8010196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_8010196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010196 prefixEnd_8010196 := by exact prefixLift 8010196
  have htrace : WordTrace (prefixWord ++ tailWord_8010196) baseStart_8010196 baseEnd_8010196 := by
    simpa [prefixWord, tailWord_8010196, baseEnd_8010196] using wordTrace_append hprefix tailTrace_8010196
  have hstable : (prefixWord ++ tailWord_8010196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010196).length < 2 ^ (prefixWord ++ tailWord_8010196).sum := by decide
  have hdescent : baseEnd_8010196 < baseStart_8010196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010209 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 2, 8]
def baseStart_8010209 : Nat := 118140960795 + 8010209 * 2 ^ 59
def prefixEnd_8010209 : Nat := 4983230072969 + 3 ^ 40 * 8010209 * 2
def baseEnd_8010209 : Nat := 1371029119990185251383075

theorem tailTrace_8010209 : CollatzResearch.WordTrace tailWord_8010209 prefixEnd_8010209 1371029119990185251383075 := by
  unfold tailWord_8010209
  simp only [CollatzResearch.WordTrace]
  refine ⟨292156323837388302627497681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194770882558258868418331787 292156323837388302627497681)
  ·
    refine ⟨219117242878041226970623261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292156323837388302627497681 219117242878041226970623261)
    ·
      refine ⟨82168966079265460113983723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219117242878041226970623261 82168966079265460113983723)
      ·
        refine ⟨123253449118898190170975585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82168966079265460113983723 123253449118898190170975585)
        ·
          refine ⟨92440086839173642628231689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123253449118898190170975585 92440086839173642628231689)
          ·
            refine ⟨69330065129380231971173767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92440086839173642628231689 69330065129380231971173767)
            ·
              refine ⟨103995097694070347956760651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69330065129380231971173767 103995097694070347956760651)
              ·
                refine ⟨155992646541105521935140977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103995097694070347956760651 155992646541105521935140977)
                ·
                  refine ⟨116994484905829141451355733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155992646541105521935140977 116994484905829141451355733)
                  ·
                    refine ⟨1371029119990185251383075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116994484905829141451355733 1371029119990185251383075)
                    ·
                      rfl

theorem cell23_8010209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_8010209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010209 prefixEnd_8010209 := by exact prefixLift 8010209
  have htrace : WordTrace (prefixWord ++ tailWord_8010209) baseStart_8010209 baseEnd_8010209 := by
    simpa [prefixWord, tailWord_8010209, baseEnd_8010209] using wordTrace_append hprefix tailTrace_8010209
  have hstable : (prefixWord ++ tailWord_8010209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010209).length < 2 ^ (prefixWord ++ tailWord_8010209).sum := by decide
  have hdescent : baseEnd_8010209 < baseStart_8010209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010216 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_8010216 : Nat := 118140960795 + 8010216 * 2 ^ 59
def prefixEnd_8010216 : Nat := 4983230072969 + 3 ^ 40 * 8010216 * 2
def baseEnd_8010216 : Nat := 4113090954335137226761693

theorem tailTrace_8010216 : CollatzResearch.WordTrace tailWord_8010216 prefixEnd_8010216 4113090954335137226761693 := by
  unfold tailWord_8010216
  simp only [CollatzResearch.WordTrace]
  refine ⟨146078289574181471411501251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194771052765575295215335001 146078289574181471411501251)
  ·
    refine ⟨219117434361272207117251877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146078289574181471411501251 219117434361272207117251877)
    ·
      refine ⟨41084518942738538834484727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219117434361272207117251877 41084518942738538834484727)
      ·
        refine ⟨61626778414107808251727091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41084518942738538834484727 61626778414107808251727091)
        ·
          refine ⟨92440167621161712377590637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61626778414107808251727091 92440167621161712377590637)
          ·
            refine ⟨34665062857935642141596489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92440167621161712377590637 34665062857935642141596489)
            ·
              refine ⟨25998797143451731606197367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34665062857935642141596489 25998797143451731606197367)
              ·
                refine ⟨38998195715177597409296051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25998797143451731606197367 38998195715177597409296051)
                ·
                  refine ⟨58497293572766396113944077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38998195715177597409296051 58497293572766396113944077)
                  ·
                    refine ⟨21936485089787398542729029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58497293572766396113944077 21936485089787398542729029)
                    ·
                      refine ⟨4113090954335137226761693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21936485089787398542729029 4113090954335137226761693)
                      ·
                        rfl

theorem cell23_8010216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_8010216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010216 prefixEnd_8010216 := by exact prefixLift 8010216
  have htrace : WordTrace (prefixWord ++ tailWord_8010216) baseStart_8010216 baseEnd_8010216 := by
    simpa [prefixWord, tailWord_8010216, baseEnd_8010216] using wordTrace_append hprefix tailTrace_8010216
  have hstable : (prefixWord ++ tailWord_8010216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010216).length < 2 ^ (prefixWord ++ tailWord_8010216).sum := by decide
  have hdescent : baseEnd_8010216 < baseStart_8010216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010239 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 8]
def baseStart_8010239 : Nat := 118140960795 + 8010239 * 2 ^ 59
def prefixEnd_8010239 : Nat := 4983230072969 + 3 ^ 40 * 8010239 * 2
def baseEnd_8010239 : Nat := 457011418265576737419343

theorem tailTrace_8010239 : CollatzResearch.WordTrace tailWord_8010239 prefixEnd_8010239 457011418265576737419343 := by
  unfold tailWord_8010239
  simp only [CollatzResearch.WordTrace]
  refine ⟨292157418027279617751089771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194771612018186411834059847 292157418027279617751089771)
  ·
    refine ⟨438236127040919426626634657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292157418027279617751089771 438236127040919426626634657)
    ·
      refine ⟨328677095280689569969975993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438236127040919426626634657 328677095280689569969975993)
      ·
        refine ⟨246507821460517177477481995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328677095280689569969975993 246507821460517177477481995)
        ·
          refine ⟨369761732190775766216222993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246507821460517177477481995 369761732190775766216222993)
          ·
            refine ⟨277321299143081824662167245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369761732190775766216222993 277321299143081824662167245)
            ·
              refine ⟨103995487178655684248312717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277321299143081824662167245 103995487178655684248312717)
              ·
                refine ⟨38998307691995881593117269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103995487178655684248312717 38998307691995881593117269)
                ·
                  refine ⟨457011418265576737419343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38998307691995881593117269 457011418265576737419343)
                  ·
                    rfl

theorem cell23_8010239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 8].length) (baseStart_8010239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010239 prefixEnd_8010239 := by exact prefixLift 8010239
  have htrace : WordTrace (prefixWord ++ tailWord_8010239) baseStart_8010239 baseEnd_8010239 := by
    simpa [prefixWord, tailWord_8010239, baseEnd_8010239] using wordTrace_append hprefix tailTrace_8010239
  have hstable : (prefixWord ++ tailWord_8010239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010239).length < 2 ^ (prefixWord ++ tailWord_8010239).sum := by decide
  have hdescent : baseEnd_8010239 < baseStart_8010239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010266 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_8010266 : Nat := 118140960795 + 8010266 * 2 ^ 59
def prefixEnd_8010266 : Nat := 4983230072969 + 3 ^ 40 * 8010266 * 2
def baseEnd_8010266 : Nat := 4113116628367862031136463

theorem tailTrace_8010266 : CollatzResearch.WordTrace tailWord_8010266 prefixEnd_8010266 4113116628367862031136463 := by
  unfold tailWord_8010266
  simp only [CollatzResearch.WordTrace]
  refine ⟨73039600699545450340580663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194772268532121200908215101 73039600699545450340580663)
  ·
    refine ⟨109559401049318175510870995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73039600699545450340580663 109559401049318175510870995)
    ·
      refine ⟨164339101573977263266306493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109559401049318175510870995 164339101573977263266306493)
      ·
        refine ⟨61627163090241473724864935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164339101573977263266306493 61627163090241473724864935)
        ·
          refine ⟨92440744635362210587297403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61627163090241473724864935 92440744635362210587297403)
          ·
            refine ⟨138661116953043315880946105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92440744635362210587297403 138661116953043315880946105)
            ·
              refine ⟨103995837714782486910709579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138661116953043315880946105 103995837714782486910709579)
              ·
                refine ⟨155993756572173730366064369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103995837714782486910709579 155993756572173730366064369)
                ·
                  refine ⟨116995317429130297774548277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155993756572173730366064369 116995317429130297774548277)
                  ·
                    refine ⟨10968311008980965416363901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116995317429130297774548277 10968311008980965416363901)
                    ·
                      refine ⟨4113116628367862031136463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10968311008980965416363901 4113116628367862031136463)
                      ·
                        rfl

theorem cell23_8010266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_8010266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010266 prefixEnd_8010266 := by exact prefixLift 8010266
  have htrace : WordTrace (prefixWord ++ tailWord_8010266) baseStart_8010266 baseEnd_8010266 := by
    simpa [prefixWord, tailWord_8010266, baseEnd_8010266] using wordTrace_append hprefix tailTrace_8010266
  have hstable : (prefixWord ++ tailWord_8010266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010266).length < 2 ^ (prefixWord ++ tailWord_8010266).sum := by decide
  have hdescent : baseEnd_8010266 < baseStart_8010266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010294 : List Nat := [5, 1, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_8010294 : Nat := 118140960795 + 8010294 * 2 ^ 59
def prefixEnd_8010294 : Nat := 4983230072969 + 3 ^ 40 * 8010294 * 2
def baseEnd_8010294 : Nat := 1371043668608729307195445

theorem tailTrace_8010294 : CollatzResearch.WordTrace tailWord_8010294 prefixEnd_8010294 1371043668608729307195445 := by
  unfold tailWord_8010294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18259964002630022634021371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194772949361386908096227957 18259964002630022634021371)
  ·
    refine ⟨27389946003945033951032057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18259964002630022634021371 27389946003945033951032057)
    ·
      refine ⟨20542459502958775463274043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27389946003945033951032057 20542459502958775463274043)
      ·
        refine ⟨30813689254438163194911065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20542459502958775463274043 30813689254438163194911065)
        ·
          refine ⟨23110266940828622396183299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30813689254438163194911065 23110266940828622396183299)
          ·
            refine ⟨34665400411242933594274949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23110266940828622396183299 34665400411242933594274949)
            ·
              refine ⟨6499762577108050048926553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34665400411242933594274949 6499762577108050048926553)
              ·
                refine ⟨4874821932831037536694915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6499762577108050048926553 4874821932831037536694915)
                ·
                  refine ⟨7312232899246556305042373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874821932831037536694915 7312232899246556305042373)
                  ·
                    refine ⟨1371043668608729307195445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7312232899246556305042373 1371043668608729307195445)
                    ·
                      rfl

theorem cell23_8010294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_8010294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010294 prefixEnd_8010294 := by exact prefixLift 8010294
  have htrace : WordTrace (prefixWord ++ tailWord_8010294) baseStart_8010294 baseEnd_8010294 := by
    simpa [prefixWord, tailWord_8010294, baseEnd_8010294] using wordTrace_append hprefix tailTrace_8010294
  have hstable : (prefixWord ++ tailWord_8010294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010294).length < 2 ^ (prefixWord ++ tailWord_8010294).sum := by decide
  have hdescent : baseEnd_8010294 < baseStart_8010294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010317 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_8010317 : Nat := 118140960795 + 8010317 * 2 ^ 59
def prefixEnd_8010317 : Nat := 4983230072969 + 3 ^ 40 * 8010317 * 2
def baseEnd_8010317 : Nat := 4113142815881241331598729

theorem tailTrace_8010317 : CollatzResearch.WordTrace tailWord_8010317 prefixEnd_8010317 4113142815881241331598729 := by
  unfold tailWord_8010317
  simp only [CollatzResearch.WordTrace]
  refine ⟨292160262920997037072429205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194773508613998024714952803 292160262920997037072429205)
  ·
    refine ⟨13695012324421736112770119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 292160262920997037072429205 13695012324421736112770119)
    ·
      refine ⟨20542518486632604169155179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13695012324421736112770119 20542518486632604169155179)
      ·
        refine ⟨30813777729948906253732769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20542518486632604169155179 30813777729948906253732769)
        ·
          refine ⟨23110333297461679690299577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30813777729948906253732769 23110333297461679690299577)
          ·
            refine ⟨17332749973096259767724683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23110333297461679690299577 17332749973096259767724683)
            ·
              refine ⟨25999124959644389651587025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17332749973096259767724683 25999124959644389651587025)
              ·
                refine ⟨19499343719733292238690269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25999124959644389651587025 19499343719733292238690269)
                ·
                  refine ⟨7312253894899984589508851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19499343719733292238690269 7312253894899984589508851)
                  ·
                    refine ⟨10968380842349976884263277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7312253894899984589508851 10968380842349976884263277)
                    ·
                      refine ⟨4113142815881241331598729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10968380842349976884263277 4113142815881241331598729)
                      ·
                        rfl

theorem cell23_8010317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_8010317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010317 prefixEnd_8010317 := by exact prefixLift 8010317
  have htrace : WordTrace (prefixWord ++ tailWord_8010317) baseStart_8010317 baseEnd_8010317 := by
    simpa [prefixWord, tailWord_8010317, baseEnd_8010317] using wordTrace_append hprefix tailTrace_8010317
  have hstable : (prefixWord ++ tailWord_8010317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010317).length < 2 ^ (prefixWord ++ tailWord_8010317).sum := by decide
  have hdescent : baseEnd_8010317 < baseStart_8010317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010340 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_8010340 : Nat := 118140960795 + 8010340 * 2 ^ 59
def prefixEnd_8010340 : Nat := 4983230072969 + 3 ^ 40 * 8010340 * 2
def baseEnd_8010340 : Nat := 4113154625936294741611123

theorem tailTrace_8010340 : CollatzResearch.WordTrace tailWord_8010340 prefixEnd_8010340 4113154625936294741611123 := by
  unfold tailWord_8010340
  simp only [CollatzResearch.WordTrace]
  refine ⟨146080550899956856000258237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194774067866609141333677649 146080550899956856000258237)
  ·
    refine ⟨54780206587483821000096839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146080550899956856000258237 54780206587483821000096839)
    ·
      refine ⟨82170309881225731500145259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54780206587483821000096839 82170309881225731500145259)
      ·
        refine ⟨123255464821838597250217889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82170309881225731500145259 123255464821838597250217889)
        ·
          refine ⟨92441598616378947937663417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123255464821838597250217889 92441598616378947937663417)
          ·
            refine ⟨69331198962284210953247563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92441598616378947937663417 69331198962284210953247563)
            ·
              refine ⟨103996798443426316429871345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69331198962284210953247563 103996798443426316429871345)
              ·
                refine ⟨77997598832569737322403509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103996798443426316429871345 77997598832569737322403509)
                ·
                  refine ⟨7312274890553412873975329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77997598832569737322403509 7312274890553412873975329)
                  ·
                    refine ⟨5484206167915059655481497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7312274890553412873975329 5484206167915059655481497)
                    ·
                      refine ⟨4113154625936294741611123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5484206167915059655481497 4113154625936294741611123)
                      ·
                        rfl

theorem cell23_8010340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_8010340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010340 prefixEnd_8010340 := by exact prefixLift 8010340
  have htrace : WordTrace (prefixWord ++ tailWord_8010340) baseStart_8010340 baseEnd_8010340 := by
    simpa [prefixWord, tailWord_8010340, baseEnd_8010340] using wordTrace_append hprefix tailTrace_8010340
  have hstable : (prefixWord ++ tailWord_8010340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010340).length < 2 ^ (prefixWord ++ tailWord_8010340).sum := by decide
  have hdescent : baseEnd_8010340 < baseStart_8010340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010346 : List Nat := [3, 1, 3, 2, 1, 1, 12]
def baseStart_8010346 : Nat := 118140960795 + 8010346 * 2 ^ 59
def prefixEnd_8010346 : Nat := 4983230072969 + 3 ^ 40 * 8010346 * 2
def baseEnd_8010346 : Nat := 50779724775558292816495

theorem tailTrace_8010346 : CollatzResearch.WordTrace tailWord_8010346 prefixEnd_8010346 50779724775558292816495 := by
  unfold tailWord_8010346
  simp only [CollatzResearch.WordTrace]
  refine ⟨73040330159472993756308723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194774213758594650016823261 73040330159472993756308723)
  ·
    refine ⟨109560495239209490634463085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73040330159472993756308723 109560495239209490634463085)
    ·
      refine ⟨41085185714703558987923657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109560495239209490634463085 41085185714703558987923657)
      ·
        refine ⟨30813889286027669240942743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41085185714703558987923657 30813889286027669240942743)
        ·
          refine ⟨46220833929041503861414115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30813889286027669240942743 46220833929041503861414115)
          ·
            refine ⟨69331250893562255792121173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46220833929041503861414115 69331250893562255792121173)
            ·
              refine ⟨50779724775558292816495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 69331250893562255792121173 50779724775558292816495)
              ·
                rfl

theorem cell23_8010346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 12].length) (baseStart_8010346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010346 prefixEnd_8010346 := by exact prefixLift 8010346
  have htrace : WordTrace (prefixWord ++ tailWord_8010346) baseStart_8010346 baseEnd_8010346 := by
    simpa [prefixWord, tailWord_8010346, baseEnd_8010346] using wordTrace_append hprefix tailTrace_8010346
  have hstable : (prefixWord ++ tailWord_8010346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010346).length < 2 ^ (prefixWord ++ tailWord_8010346).sum := by decide
  have hdescent : baseEnd_8010346 < baseStart_8010346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010350 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_8010350 : Nat := 118140960795 + 8010350 * 2 ^ 59
def prefixEnd_8010350 : Nat := 4983230072969 + 3 ^ 40 * 8010350 * 2
def baseEnd_8010350 : Nat := 1371053253580946567495359

theorem tailTrace_8010350 : CollatzResearch.WordTrace tailWord_8010350 prefixEnd_8010350 1371053253580946567495359 := by
  unfold tailWord_8010350
  simp only [CollatzResearch.WordTrace]
  refine ⟨36520183316234685463547563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194774311019918322472253669 36520183316234685463547563)
  ·
    refine ⟨54780274974352028195321345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36520183316234685463547563 54780274974352028195321345)
    ·
      refine ⟨41085206230764021146491009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54780274974352028195321345 41085206230764021146491009)
      ·
        refine ⟨30813904673073015859868257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41085206230764021146491009 30813904673073015859868257)
        ·
          refine ⟨23110428504804761894901193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30813904673073015859868257 23110428504804761894901193)
          ·
            refine ⟨17332821378603571421175895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23110428504804761894901193 17332821378603571421175895)
            ·
              refine ⟨25999232067905357131763843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17332821378603571421175895 25999232067905357131763843)
              ·
                refine ⟨38998848101858035697645765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25999232067905357131763843 38998848101858035697645765)
                ·
                  refine ⟨7312284019098381693308581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38998848101858035697645765 7312284019098381693308581)
                  ·
                    refine ⟨1371053253580946567495359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7312284019098381693308581 1371053253580946567495359)
                    ·
                      rfl

theorem cell23_8010350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_8010350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010350 prefixEnd_8010350 := by exact prefixLift 8010350
  have htrace : WordTrace (prefixWord ++ tailWord_8010350) baseStart_8010350 baseEnd_8010350 := by
    simpa [prefixWord, tailWord_8010350, baseEnd_8010350] using wordTrace_append hprefix tailTrace_8010350
  have hstable : (prefixWord ++ tailWord_8010350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010350).length < 2 ^ (prefixWord ++ tailWord_8010350).sum := by decide
  have hdescent : baseEnd_8010350 < baseStart_8010350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010416 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_8010416 : Nat := 118140960795 + 8010416 * 2 ^ 59
def prefixEnd_8010416 : Nat := 4983230072969 + 3 ^ 40 * 8010416 * 2
def baseEnd_8010416 : Nat := 4113193650466036444260773

theorem tailTrace_8010416 : CollatzResearch.WordTrace tailWord_8010416 prefixEnd_8010416 4113193650466036444260773 := by
  unfold tailWord_8010416
  simp only [CollatzResearch.WordTrace]
  refine ⟨146081936873819188490141551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194775915831758917986855401 146081936873819188490141551)
  ·
    refine ⟨219122905310728782735212327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146081936873819188490141551 219122905310728782735212327)
    ·
      refine ⟨328684357966093174102818491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219122905310728782735212327 328684357966093174102818491)
      ·
        refine ⟨493026536949139761154227737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328684357966093174102818491 493026536949139761154227737)
        ·
          refine ⟨369769902711854820865670803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493026536949139761154227737 369769902711854820865670803)
          ·
            refine ⟨554654854067782231298506205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369769902711854820865670803 554654854067782231298506205)
            ·
              refine ⟨207995570275418336736939827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554654854067782231298506205 207995570275418336736939827)
              ·
                refine ⟨311993355413127505105409741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207995570275418336736939827 311993355413127505105409741)
                ·
                  refine ⟨116997508279922814414528653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311993355413127505105409741 116997508279922814414528653)
                  ·
                    refine ⟨43874065604971055405448245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116997508279922814414528653 43874065604971055405448245)
                    ·
                      refine ⟨4113193650466036444260773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43874065604971055405448245 4113193650466036444260773)
                      ·
                        rfl

theorem cell23_8010416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_8010416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010416 prefixEnd_8010416 := by exact prefixLift 8010416
  have htrace : WordTrace (prefixWord ++ tailWord_8010416) baseStart_8010416 baseEnd_8010416 := by
    simpa [prefixWord, tailWord_8010416, baseEnd_8010416] using wordTrace_append hprefix tailTrace_8010416
  have hstable : (prefixWord ++ tailWord_8010416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010416).length < 2 ^ (prefixWord ++ tailWord_8010416).sum := by decide
  have hdescent : baseEnd_8010416 < baseStart_8010416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010523 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 3]
def baseStart_8010523 : Nat := 118140960795 + 8010523 * 2 ^ 59
def prefixEnd_8010523 : Nat := 4983230072969 + 3 ^ 40 * 8010523 * 2
def baseEnd_8010523 : Nat := 4113248592896067525622781

theorem tailTrace_8010523 : CollatzResearch.WordTrace tailWord_8010523 prefixEnd_8010523 4113248592896067525622781 := by
  unfold tailWord_8010523
  simp only [CollatzResearch.WordTrace]
  refine ⟨292167776358250734254428223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194778517572167156169618815 292167776358250734254428223)
  ·
    refine ⟨438251664537376101381642335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292167776358250734254428223 438251664537376101381642335)
    ·
      refine ⟨657377496806064152072463503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438251664537376101381642335 657377496806064152072463503)
      ·
        refine ⟨986066245209096228108695255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657377496806064152072463503 986066245209096228108695255)
        ·
          refine ⟨1479099367813644342163042883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986066245209096228108695255 1479099367813644342163042883)
          ·
            refine ⟨2218649051720466513244564325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479099367813644342163042883 2218649051720466513244564325)
            ·
              refine ⟨415996697197587471233355811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2218649051720466513244564325 415996697197587471233355811)
              ·
                refine ⟨623995045796381206850033717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415996697197587471233355811 623995045796381206850033717)
                ·
                  refine ⟨58499535543410738142190661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 623995045796381206850033717 58499535543410738142190661)
                  ·
                    refine ⟨10968662914389513401660749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58499535543410738142190661 10968662914389513401660749)
                    ·
                      refine ⟨4113248592896067525622781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10968662914389513401660749 4113248592896067525622781)
                      ·
                        rfl

theorem cell23_8010523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 3].length) (baseStart_8010523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010523 prefixEnd_8010523 := by exact prefixLift 8010523
  have htrace : WordTrace (prefixWord ++ tailWord_8010523) baseStart_8010523 baseEnd_8010523 := by
    simpa [prefixWord, tailWord_8010523, baseEnd_8010523] using wordTrace_append hprefix tailTrace_8010523
  have hstable : (prefixWord ++ tailWord_8010523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010523).length < 2 ^ (prefixWord ++ tailWord_8010523).sum := by decide
  have hdescent : baseEnd_8010523 < baseStart_8010523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010533 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_8010533 : Nat := 118140960795 + 8010533 * 2 ^ 59
def prefixEnd_8010533 : Nat := 4983230072969 + 3 ^ 40 * 8010533 * 2
def baseEnd_8010533 : Nat := 4113253727702612486497735

theorem tailTrace_8010533 : CollatzResearch.WordTrace tailWord_8010533 prefixEnd_8010533 4113253727702612486497735 := by
  unfold tailWord_8010533
  simp only [CollatzResearch.WordTrace]
  refine ⟨292168141088214505962292253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194778760725476337308194835 292168141088214505962292253)
  ·
    refine ⟨109563052908080439735859595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292168141088214505962292253 109563052908080439735859595)
    ·
      refine ⟨164344579362120659603789393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109563052908080439735859595 164344579362120659603789393)
      ·
        refine ⟨123258434521590494702842045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164344579362120659603789393 123258434521590494702842045)
        ·
          refine ⟨46221912945596435513565767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123258434521590494702842045 46221912945596435513565767)
          ·
            refine ⟨69332869418394653270348651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46221912945596435513565767 69332869418394653270348651)
            ·
              refine ⟨103999304127591979905522977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69332869418394653270348651 103999304127591979905522977)
              ·
                refine ⟨77999478095693984929142233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103999304127591979905522977 77999478095693984929142233)
                ·
                  refine ⟨58499608571770488696856675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77999478095693984929142233 58499608571770488696856675)
                  ·
                    refine ⟨87749412857655733045285013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58499608571770488696856675 87749412857655733045285013)
                    ·
                      refine ⟨4113253727702612486497735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87749412857655733045285013 4113253727702612486497735)
                      ·
                        rfl

theorem cell23_8010533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_8010533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010533 prefixEnd_8010533 := by exact prefixLift 8010533
  have htrace : WordTrace (prefixWord ++ tailWord_8010533) baseStart_8010533 baseEnd_8010533 := by
    simpa [prefixWord, tailWord_8010533, baseEnd_8010533] using wordTrace_append hprefix tailTrace_8010533
  have hstable : (prefixWord ++ tailWord_8010533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010533).length < 2 ^ (prefixWord ++ tailWord_8010533).sum := by decide
  have hdescent : baseEnd_8010533 < baseStart_8010533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010620 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_8010620 : Nat := 118140960795 + 8010620 * 2 ^ 59
def prefixEnd_8010620 : Nat := 4983230072969 + 3 ^ 40 * 8010620 * 2
def baseEnd_8010620 : Nat := 1371099466839851215369945

theorem tailTrace_8010620 : CollatzResearch.WordTrace tailWord_8010620 prefixEnd_8010620 1371099466839851215369945 := by
  unfold tailWord_8010620
  simp only [CollatzResearch.WordTrace]
  refine ⟨146085657119449659910354657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194780876159266213213806209 146085657119449659910354657)
  ·
    refine ⟨109564242839587244932765993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146085657119449659910354657 109564242839587244932765993)
    ·
      refine ⟨82173182129690433699574495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109564242839587244932765993 82173182129690433699574495)
      ·
        refine ⟨123259773194535650549361743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82173182129690433699574495 123259773194535650549361743)
        ·
          refine ⟨184889659791803475824042615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123259773194535650549361743 184889659791803475824042615)
          ·
            refine ⟨277334489687705213736063923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184889659791803475824042615 277334489687705213736063923)
            ·
              refine ⟨416001734531557820604095885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277334489687705213736063923 416001734531557820604095885)
              ·
                refine ⟨156000650449334182726535957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 416001734531557820604095885 156000650449334182726535957)
                ·
                  refine ⟨7312530489812539815306373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156000650449334182726535957 7312530489812539815306373)
                  ·
                    refine ⟨1371099466839851215369945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7312530489812539815306373 1371099466839851215369945)
                    ·
                      rfl

theorem cell23_8010620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_8010620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010620 prefixEnd_8010620 := by exact prefixLift 8010620
  have htrace : WordTrace (prefixWord ++ tailWord_8010620) baseStart_8010620 baseEnd_8010620 := by
    simpa [prefixWord, tailWord_8010620, baseEnd_8010620] using wordTrace_append hprefix tailTrace_8010620
  have hstable : (prefixWord ++ tailWord_8010620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010620).length < 2 ^ (prefixWord ++ tailWord_8010620).sum := by decide
  have hdescent : baseEnd_8010620 < baseStart_8010620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010633 : List Nat := [1, 2, 1, 1, 5, 13]
def baseStart_8010633 : Nat := 118140960795 + 8010633 * 2 ^ 59
def prefixEnd_8010633 : Nat := 4983230072969 + 3 ^ 40 * 8010633 * 2
def baseEnd_8010633 : Nat := 16927181381761572408425

theorem tailTrace_8010633 : CollatzResearch.WordTrace tailWord_8010633 prefixEnd_8010633 16927181381761572408425 := by
  unfold tailWord_8010633
  simp only [CollatzResearch.WordTrace]
  refine ⟨292171788387852223040932553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194781192258568148693955035 292171788387852223040932553)
  ·
    refine ⟨219128841290889167280699415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292171788387852223040932553 219128841290889167280699415)
    ·
      refine ⟨328693261936333750921049123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219128841290889167280699415 328693261936333750921049123)
      ·
        refine ⟨493039892904500626381573685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328693261936333750921049123 493039892904500626381573685)
        ·
          refine ⟨46222489959796933723272533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 493039892904500626381573685 46222489959796933723272533)
          ·
            refine ⟨16927181381761572408425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 46222489959796933723272533 16927181381761572408425)
            ·
              rfl

theorem cell23_8010633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 13].length) (baseStart_8010633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010633 prefixEnd_8010633 := by exact prefixLift 8010633
  have htrace : WordTrace (prefixWord ++ tailWord_8010633) baseStart_8010633 baseEnd_8010633 := by
    simpa [prefixWord, tailWord_8010633, baseEnd_8010633] using wordTrace_append hprefix tailTrace_8010633
  have hstable : (prefixWord ++ tailWord_8010633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010633).length < 2 ^ (prefixWord ++ tailWord_8010633).sum := by decide
  have hdescent : baseEnd_8010633 < baseStart_8010633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010643 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 7]
def baseStart_8010643 : Nat := 118140960795 + 8010643 * 2 ^ 59
def prefixEnd_8010643 : Nat := 4983230072969 + 3 ^ 40 * 8010643 * 2
def baseEnd_8010643 : Nat := 4113310210574607056122229

theorem tailTrace_8010643 : CollatzResearch.WordTrace tailWord_8010643 prefixEnd_8010643 4113310210574607056122229 := by
  unfold tailWord_8010643
  simp only [CollatzResearch.WordTrace]
  refine ⟨292172153117815994748796583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194781435411877329832531055 292172153117815994748796583)
  ·
    refine ⟨438258229676723992123194875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292172153117815994748796583 438258229676723992123194875)
    ·
      refine ⟨657387344515085988184792313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438258229676723992123194875 657387344515085988184792313)
      ·
        refine ⟨493040508386314491138594235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657387344515085988184792313 493040508386314491138594235)
        ·
          refine ⟨739560762579471736707891353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493040508386314491138594235 739560762579471736707891353)
          ·
            refine ⟨554670571934603802530918515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739560762579471736707891353 554670571934603802530918515)
            ·
              refine ⟨832005857901905703796377773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554670571934603802530918515 832005857901905703796377773)
              ·
                refine ⟨312002196713214638923641665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 832005857901905703796377773 312002196713214638923641665)
                ·
                  refine ⟨234001647534910979192731249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312002196713214638923641665 234001647534910979192731249)
                  ·
                    refine ⟨175501235651183234394548437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234001647534910979192731249 175501235651183234394548437)
                    ·
                      refine ⟨4113310210574607056122229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 175501235651183234394548437 4113310210574607056122229)
                      ·
                        rfl

theorem cell23_8010643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_8010643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010643 prefixEnd_8010643 := by exact prefixLift 8010643
  have htrace : WordTrace (prefixWord ++ tailWord_8010643) baseStart_8010643 baseEnd_8010643 := by
    simpa [prefixWord, tailWord_8010643, baseEnd_8010643] using wordTrace_append hprefix tailTrace_8010643
  have hstable : (prefixWord ++ tailWord_8010643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010643).length < 2 ^ (prefixWord ++ tailWord_8010643).sum := by decide
  have hdescent : baseEnd_8010643 < baseStart_8010643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010657 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_8010657 : Nat := 118140960795 + 8010657 * 2 ^ 59
def prefixEnd_8010657 : Nat := 4983230072969 + 3 ^ 40 * 8010657 * 2
def baseEnd_8010657 : Nat := 4113317399303770001347165

theorem tailTrace_8010657 : CollatzResearch.WordTrace tailWord_8010657 prefixEnd_8010657 4113317399303770001347165 := by
  unfold tailWord_8010657
  simp only [CollatzResearch.WordTrace]
  refine ⟨292172663739765275139806225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194781775826510183426537483 292172663739765275139806225)
  ·
    refine ⟨219129497804823956354854669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292172663739765275139806225 219129497804823956354854669)
    ·
      refine ⟨82173561676808983633070501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219129497804823956354854669 82173561676808983633070501)
      ·
        refine ⟨15407542814401684431200719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82173561676808983633070501 15407542814401684431200719)
        ·
          refine ⟨23111314221602526646801079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15407542814401684431200719 23111314221602526646801079)
          ·
            refine ⟨34666971332403789970201619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23111314221602526646801079 34666971332403789970201619)
            ·
              refine ⟨52000456998605684955302429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34666971332403789970201619 52000456998605684955302429)
              ·
                refine ⟨19500171374477131858238411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52000456998605684955302429 19500171374477131858238411)
                ·
                  refine ⟨29250257061715697787357617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19500171374477131858238411 29250257061715697787357617)
                  ·
                    refine ⟨21937692796286773340518213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29250257061715697787357617 21937692796286773340518213)
                    ·
                      refine ⟨4113317399303770001347165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21937692796286773340518213 4113317399303770001347165)
                      ·
                        rfl

theorem cell23_8010657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_8010657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010657 prefixEnd_8010657 := by exact prefixLift 8010657
  have htrace : WordTrace (prefixWord ++ tailWord_8010657) baseStart_8010657 baseEnd_8010657 := by
    simpa [prefixWord, tailWord_8010657, baseEnd_8010657] using wordTrace_append hprefix tailTrace_8010657
  have hstable : (prefixWord ++ tailWord_8010657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010657).length < 2 ^ (prefixWord ++ tailWord_8010657).sum := by decide
  have hdescent : baseEnd_8010657 < baseStart_8010657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010677 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_8010677 : Nat := 118140960795 + 8010677 * 2 ^ 59
def prefixEnd_8010677 : Nat := 4983230072969 + 3 ^ 40 * 8010677 * 2
def baseEnd_8010677 : Nat := 4113327668916859923097073

theorem tailTrace_8010677 : CollatzResearch.WordTrace tailWord_8010677 prefixEnd_8010677 4113327668916859923097073 := by
  unfold tailWord_8010677
  simp only [CollatzResearch.WordTrace]
  refine ⟨292173393199692818555534285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194782262133128545703689523 292173393199692818555534285)
  ·
    refine ⟨109565022449884806958325357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292173393199692818555534285 109565022449884806958325357)
    ·
      refine ⟨41086883418706802609372009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109565022449884806958325357 41086883418706802609372009)
      ·
        refine ⟨30815162564030101957029007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41086883418706802609372009 30815162564030101957029007)
        ·
          refine ⟨46222743846045152935543511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30815162564030101957029007 46222743846045152935543511)
          ·
            refine ⟨69334115769067729403315267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46222743846045152935543511 69334115769067729403315267)
            ·
              refine ⟨104001173653601594104972901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69334115769067729403315267 104001173653601594104972901)
              ·
                refine ⟨19500220060050298894682419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104001173653601594104972901 19500220060050298894682419)
                ·
                  refine ⟨29250330090075448342023629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19500220060050298894682419 29250330090075448342023629)
                  ·
                    refine ⟨10968873783778293128258861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29250330090075448342023629 10968873783778293128258861)
                    ·
                      refine ⟨4113327668916859923097073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10968873783778293128258861 4113327668916859923097073)
                      ·
                        rfl

theorem cell23_8010677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_8010677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010677 prefixEnd_8010677 := by exact prefixLift 8010677
  have htrace : WordTrace (prefixWord ++ tailWord_8010677) baseStart_8010677 baseEnd_8010677 := by
    simpa [prefixWord, tailWord_8010677, baseEnd_8010677] using wordTrace_append hprefix tailTrace_8010677
  have hstable : (prefixWord ++ tailWord_8010677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010677).length < 2 ^ (prefixWord ++ tailWord_8010677).sum := by decide
  have hdescent : baseEnd_8010677 < baseStart_8010677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010681 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 1, 2, 3]
def baseStart_8010681 : Nat := 118140960795 + 8010681 * 2 ^ 59
def prefixEnd_8010681 : Nat := 4983230072969 + 3 ^ 40 * 8010681 * 2
def baseEnd_8010681 : Nat := 4113329722839477907447055

theorem tailTrace_8010681 : CollatzResearch.WordTrace tailWord_8010681 prefixEnd_8010681 4113329722839477907447055 := by
  unfold tailWord_8010681
  simp only [CollatzResearch.WordTrace]
  refine ⟨292173539091678327238679897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194782359394452218159119931 292173539091678327238679897)
  ·
    refine ⟨219130154318758745429009923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292173539091678327238679897 219130154318758745429009923)
    ·
      refine ⟨328695231478138118143514885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219130154318758745429009923 328695231478138118143514885)
      ·
        refine ⟨61630355902150897151909041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328695231478138118143514885 61630355902150897151909041)
        ·
          refine ⟨46222766926613172863931781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61630355902150897151909041 46222766926613172863931781)
          ·
            refine ⟨8666768798739969911987209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46222766926613172863931781 8666768798739969911987209)
            ·
              refine ⟨6500076599054977433990407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8666768798739969911987209 6500076599054977433990407)
              ·
                refine ⟨9750114898582466150985611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6500076599054977433990407 9750114898582466150985611)
                ·
                  refine ⟨14625172347873699226478417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9750114898582466150985611 14625172347873699226478417)
                  ·
                    refine ⟨10968879260905274419858813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14625172347873699226478417 10968879260905274419858813)
                    ·
                      refine ⟨4113329722839477907447055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10968879260905274419858813 4113329722839477907447055)
                      ·
                        rfl

theorem cell23_8010681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_8010681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010681 prefixEnd_8010681 := by exact prefixLift 8010681
  have htrace : WordTrace (prefixWord ++ tailWord_8010681) baseStart_8010681 baseEnd_8010681 := by
    simpa [prefixWord, tailWord_8010681, baseEnd_8010681] using wordTrace_append hprefix tailTrace_8010681
  have hstable : (prefixWord ++ tailWord_8010681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010681).length < 2 ^ (prefixWord ++ tailWord_8010681).sum := by decide
  have hdescent : baseEnd_8010681 < baseStart_8010681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010687 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 5, 3, 2]
def baseStart_8010687 : Nat := 118140960795 + 8010687 * 2 ^ 59
def prefixEnd_8010687 : Nat := 4983230072969 + 3 ^ 40 * 8010687 * 2
def baseEnd_8010687 : Nat := 4113332803723404883972027

theorem tailTrace_8010687 : CollatzResearch.WordTrace tailWord_8010687 prefixEnd_8010687 4113332803723404883972027 := by
  unfold tailWord_8010687
  simp only [CollatzResearch.WordTrace]
  refine ⟨292173757929656590263398315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194782505286437726842265543 292173757929656590263398315)
  ·
    refine ⟨438260636894484885395097473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292173757929656590263398315 438260636894484885395097473)
    ·
      refine ⟨328695477670863664046323105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438260636894484885395097473 328695477670863664046323105)
      ·
        refine ⟨246521608253147748034742329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328695477670863664046323105 246521608253147748034742329)
        ·
          refine ⟨184891206189860811026056747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246521608253147748034742329 184891206189860811026056747)
          ·
            refine ⟨277336809284791216539085121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184891206189860811026056747 277336809284791216539085121)
            ·
              refine ⟨208002606963593412404313841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277336809284791216539085121 208002606963593412404313841)
              ·
                refine ⟨156001955222695059303235381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208002606963593412404313841 156001955222695059303235381)
                ·
                  refine ⟨14625183302127661809678317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156001955222695059303235381 14625183302127661809678317)
                  ·
                    refine ⟨5484443738297873178629369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14625183302127661809678317 5484443738297873178629369)
                    ·
                      refine ⟨4113332803723404883972027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5484443738297873178629369 4113332803723404883972027)
                      ·
                        rfl

theorem cell23_8010687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_8010687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010687 prefixEnd_8010687 := by exact prefixLift 8010687
  have htrace : WordTrace (prefixWord ++ tailWord_8010687) baseStart_8010687 baseEnd_8010687 := by
    simpa [prefixWord, tailWord_8010687, baseEnd_8010687] using wordTrace_append hprefix tailTrace_8010687
  have hstable : (prefixWord ++ tailWord_8010687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010687).length < 2 ^ (prefixWord ++ tailWord_8010687).sum := by decide
  have hdescent : baseEnd_8010687 < baseStart_8010687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010737 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_8010737 : Nat := 118140960795 + 8010737 * 2 ^ 59
def prefixEnd_8010737 : Nat := 4983230072969 + 3 ^ 40 * 8010737 * 2
def baseEnd_8010737 : Nat := 4113358477756129688346797

theorem tailTrace_8010737 : CollatzResearch.WordTrace tailWord_8010737 prefixEnd_8010737 4113358477756129688346797 := by
  unfold tailWord_8010737
  simp only [CollatzResearch.WordTrace]
  refine ⟨292175581579475448802718465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194783721052983632535145643 292175581579475448802718465)
  ·
    refine ⟨219131686184606586602038849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292175581579475448802718465 219131686184606586602038849)
    ·
      refine ⟨164348764638454939951529137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219131686184606586602038849 164348764638454939951529137)
      ·
        refine ⟨123261573478841204963646853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164348764638454939951529137 123261573478841204963646853)
        ·
          refine ⟨23111545027282725930683785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123261573478841204963646853 23111545027282725930683785)
          ·
            refine ⟨17333658770462044448012839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23111545027282725930683785 17333658770462044448012839)
            ·
              refine ⟨26000488155693066672019259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17333658770462044448012839 26000488155693066672019259)
              ·
                refine ⟨39000732233539600008028889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26000488155693066672019259 39000732233539600008028889)
                ·
                  refine ⟨29250549175154700006021667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39000732233539600008028889 29250549175154700006021667)
                  ·
                    refine ⟨43875823762732050009032501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29250549175154700006021667 43875823762732050009032501)
                    ·
                      refine ⟨4113358477756129688346797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43875823762732050009032501 4113358477756129688346797)
                      ·
                        rfl

theorem cell23_8010737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_8010737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010737 prefixEnd_8010737 := by exact prefixLift 8010737
  have htrace : WordTrace (prefixWord ++ tailWord_8010737) baseStart_8010737 baseEnd_8010737 := by
    simpa [prefixWord, tailWord_8010737, baseEnd_8010737] using wordTrace_append hprefix tailTrace_8010737
  have hstable : (prefixWord ++ tailWord_8010737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010737).length < 2 ^ (prefixWord ++ tailWord_8010737).sum := by decide
  have hdescent : baseEnd_8010737 < baseStart_8010737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010787 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 2, 5]
def baseStart_8010787 : Nat := 118140960795 + 8010787 * 2 ^ 59
def prefixEnd_8010787 : Nat := 4983230072969 + 3 ^ 40 * 8010787 * 2
def baseEnd_8010787 : Nat := 1371128050596284830907189

theorem tailTrace_8010787 : CollatzResearch.WordTrace tailWord_8010787 prefixEnd_8010787 1371128050596284830907189 := by
  unfold tailWord_8010787
  simp only [CollatzResearch.WordTrace]
  refine ⟨292177405229294307342038615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194784936819529538228025743 292177405229294307342038615)
  ·
    refine ⟨438266107843941461013057923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292177405229294307342038615 438266107843941461013057923)
    ·
      refine ⟨657399161765912191519586885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438266107843941461013057923 657399161765912191519586885)
      ·
        refine ⟨123262342831108535909922541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657399161765912191519586885 123262342831108535909922541)
        ·
          refine ⟨46223378561665700966220953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123262342831108535909922541 46223378561665700966220953)
          ·
            refine ⟨34667533921249275724665715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46223378561665700966220953 34667533921249275724665715)
            ·
              refine ⟨52001300881873913586998573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34667533921249275724665715 52001300881873913586998573)
              ·
                refine ⟨19500487830702717595124465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52001300881873913586998573 19500487830702717595124465)
                ·
                  refine ⟨14625365873027038196343349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19500487830702717595124465 14625365873027038196343349)
                  ·
                    refine ⟨1371128050596284830907189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14625365873027038196343349 1371128050596284830907189)
                    ·
                      rfl

theorem cell23_8010787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 5].length) (baseStart_8010787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010787 prefixEnd_8010787 := by exact prefixLift 8010787
  have htrace : WordTrace (prefixWord ++ tailWord_8010787) baseStart_8010787 baseEnd_8010787 := by
    simpa [prefixWord, tailWord_8010787, baseEnd_8010787] using wordTrace_append hprefix tailTrace_8010787
  have hstable : (prefixWord ++ tailWord_8010787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010787).length < 2 ^ (prefixWord ++ tailWord_8010787).sum := by decide
  have hdescent : baseEnd_8010787 < baseStart_8010787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010814 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_8010814 : Nat := 118140960795 + 8010814 * 2 ^ 59
def prefixEnd_8010814 : Nat := 4983230072969 + 3 ^ 40 * 8010814 * 2
def baseEnd_8010814 : Nat := 4113398015766525887083943

theorem tailTrace_8010814 : CollatzResearch.WordTrace tailWord_8010814 prefixEnd_8010814 4113398015766525887083943 := by
  unfold tailWord_8010814
  simp only [CollatzResearch.WordTrace]
  refine ⟨36522298750024561369158937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194785593333464327302180997 36522298750024561369158937)
  ·
    refine ⟨27391724062518421026869203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36522298750024561369158937 27391724062518421026869203)
    ·
      refine ⟨41087586093777631540303805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27391724062518421026869203 41087586093777631540303805)
      ·
        refine ⟨15407844785166611827613927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41087586093777631540303805 15407844785166611827613927)
        ·
          refine ⟨23111767177749917741420891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15407844785166611827613927 23111767177749917741420891)
          ·
            refine ⟨34667650766624876612131337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23111767177749917741420891 34667650766624876612131337)
            ·
              refine ⟨26000738074968657459098503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34667650766624876612131337 26000738074968657459098503)
              ·
                refine ⟨39001107112452986188647755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26000738074968657459098503 39001107112452986188647755)
                ·
                  refine ⟨58501660668679479282971633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39001107112452986188647755 58501660668679479282971633)
                  ·
                    refine ⟨43876245501509609462228725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58501660668679479282971633 43876245501509609462228725)
                    ·
                      refine ⟨4113398015766525887083943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43876245501509609462228725 4113398015766525887083943)
                      ·
                        rfl

theorem cell23_8010814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_8010814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010814 prefixEnd_8010814 := by exact prefixLift 8010814
  have htrace : WordTrace (prefixWord ++ tailWord_8010814) baseStart_8010814 baseEnd_8010814 := by
    simpa [prefixWord, tailWord_8010814, baseEnd_8010814] using wordTrace_append hprefix tailTrace_8010814
  have hstable : (prefixWord ++ tailWord_8010814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010814).length < 2 ^ (prefixWord ++ tailWord_8010814).sum := by decide
  have hdescent : baseEnd_8010814 < baseStart_8010814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010824 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_8010824 : Nat := 118140960795 + 8010824 * 2 ^ 59
def prefixEnd_8010824 : Nat := 4983230072969 + 3 ^ 40 * 8010824 * 2
def baseEnd_8010824 : Nat := 4113403150573070847958897

theorem tailTrace_8010824 : CollatzResearch.WordTrace tailWord_8010824 prefixEnd_8010824 4113403150573070847958897 := by
  unfold tailWord_8010824
  simp only [CollatzResearch.WordTrace]
  refine ⟨146089377365080131330567763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194785836486773508440757017 146089377365080131330567763)
  ·
    refine ⟨219134066047620196995851645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146089377365080131330567763 219134066047620196995851645)
    ·
      refine ⟨82175274767857573873444367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219134066047620196995851645 82175274767857573873444367)
      ·
        refine ⟨123262912151786360810166551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82175274767857573873444367 123262912151786360810166551)
        ·
          refine ⟨184894368227679541215249827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123262912151786360810166551 184894368227679541215249827)
          ·
            refine ⟨277341552341519311822874741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184894368227679541215249827 277341552341519311822874741)
            ·
              refine ⟨26000770532017435483394507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 277341552341519311822874741 26000770532017435483394507)
              ·
                refine ⟨39001155798026153225091761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26000770532017435483394507 39001155798026153225091761)
                ·
                  refine ⟨29250866848519614918818821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39001155798026153225091761 29250866848519614918818821)
                  ·
                    refine ⟨5484537534097427797278529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29250866848519614918818821 5484537534097427797278529)
                    ·
                      refine ⟨4113403150573070847958897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5484537534097427797278529 4113403150573070847958897)
                      ·
                        rfl

theorem cell23_8010824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_8010824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010824 prefixEnd_8010824 := by exact prefixLift 8010824
  have htrace : WordTrace (prefixWord ++ tailWord_8010824) baseStart_8010824 baseEnd_8010824 := by
    simpa [prefixWord, tailWord_8010824, baseEnd_8010824] using wordTrace_append hprefix tailTrace_8010824
  have hstable : (prefixWord ++ tailWord_8010824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010824).length < 2 ^ (prefixWord ++ tailWord_8010824).sum := by decide
  have hdescent : baseEnd_8010824 < baseStart_8010824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010834 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_8010834 : Nat := 118140960795 + 8010834 * 2 ^ 59
def prefixEnd_8010834 : Nat := 4983230072969 + 3 ^ 40 * 8010834 * 2
def baseEnd_8010834 : Nat := 1371136095126538602944617

theorem tailTrace_8010834 : CollatzResearch.WordTrace tailWord_8010834 prefixEnd_8010834 1371136095126538602944617 := by
  unfold tailWord_8010834
  simp only [CollatzResearch.WordTrace]
  refine ⟨73044779865031008592249889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194786079640082689579333037 73044779865031008592249889)
  ·
    refine ⟨54783584898773256444187417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73044779865031008592249889 54783584898773256444187417)
    ·
      refine ⟨41087688674079942333140563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54783584898773256444187417 41087688674079942333140563)
      ·
        refine ⟨61631533011119913499710845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41087688674079942333140563 61631533011119913499710845)
        ·
          refine ⟨23111824879169967562391567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61631533011119913499710845 23111824879169967562391567)
          ·
            refine ⟨34667737318754951343587351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23111824879169967562391567 34667737318754951343587351)
            ·
              refine ⟨52001605978132427015381027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34667737318754951343587351 52001605978132427015381027)
              ·
                refine ⟨78002408967198640523071541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52001605978132427015381027 78002408967198640523071541)
                ·
                  refine ⟨7312725840674872549037957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78002408967198640523071541 7312725840674872549037957)
                  ·
                    refine ⟨1371136095126538602944617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7312725840674872549037957 1371136095126538602944617)
                    ·
                      rfl

theorem cell23_8010834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_8010834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010834 prefixEnd_8010834 := by exact prefixLift 8010834
  have htrace : WordTrace (prefixWord ++ tailWord_8010834) baseStart_8010834 baseEnd_8010834 := by
    simpa [prefixWord, tailWord_8010834, baseEnd_8010834] using wordTrace_append hprefix tailTrace_8010834
  have hstable : (prefixWord ++ tailWord_8010834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010834).length < 2 ^ (prefixWord ++ tailWord_8010834).sum := by decide
  have hdescent : baseEnd_8010834 < baseStart_8010834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010844 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_8010844 : Nat := 118140960795 + 8010844 * 2 ^ 59
def prefixEnd_8010844 : Nat := 4983230072969 + 3 ^ 40 * 8010844 * 2
def baseEnd_8010844 : Nat := 4113413420186160769708805

theorem tailTrace_8010844 : CollatzResearch.WordTrace tailWord_8010844 prefixEnd_8010844 4113413420186160769708805 := by
  unfold tailWord_8010844
  simp only [CollatzResearch.WordTrace]
  refine ⟨146089742095043903038431793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194786322793391870717909057 146089742095043903038431793)
  ·
    refine ⟨109567306571282927278823845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146089742095043903038431793 109567306571282927278823845)
    ·
      refine ⟨20543869982115548864779471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109567306571282927278823845 20543869982115548864779471)
      ·
        refine ⟨30815804973173323297169207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20543869982115548864779471 30815804973173323297169207)
        ·
          refine ⟨46223707459759984945753811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30815804973173323297169207 46223707459759984945753811)
          ·
            refine ⟨69335561189639977418630717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46223707459759984945753811 69335561189639977418630717)
            ·
              refine ⟨26000835446114991531986519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69335561189639977418630717 26000835446114991531986519)
              ·
                refine ⟨39001253169172487297979779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26000835446114991531986519 39001253169172487297979779)
                ·
                  refine ⟨58501879753758730946969669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39001253169172487297979779 58501879753758730946969669)
                  ·
                    refine ⟨10969102453829762052556813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58501879753758730946969669 10969102453829762052556813)
                    ·
                      refine ⟨4113413420186160769708805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10969102453829762052556813 4113413420186160769708805)
                      ·
                        rfl

theorem cell23_8010844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_8010844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010844 prefixEnd_8010844 := by exact prefixLift 8010844
  have htrace : WordTrace (prefixWord ++ tailWord_8010844) baseStart_8010844 baseEnd_8010844 := by
    simpa [prefixWord, tailWord_8010844, baseEnd_8010844] using wordTrace_append hprefix tailTrace_8010844
  have hstable : (prefixWord ++ tailWord_8010844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010844).length < 2 ^ (prefixWord ++ tailWord_8010844).sum := by decide
  have hdescent : baseEnd_8010844 < baseStart_8010844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010881 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 6]
def baseStart_8010881 : Nat := 118140960795 + 8010881 * 2 ^ 59
def prefixEnd_8010881 : Nat := 4983230072969 + 3 ^ 40 * 8010881 * 2
def baseEnd_8010881 : Nat := 457048046552264124994015

theorem tailTrace_8010881 : CollatzResearch.WordTrace tailWord_8010881 prefixEnd_8010881 457048046552264124994015 := by
  unfold tailWord_8010881
  simp only [CollatzResearch.WordTrace]
  refine ⟨292180833690953761395960497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194787222460635840930640331 292180833690953761395960497)
  ·
    refine ⟨219135625268215321046970373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292180833690953761395960497 219135625268215321046970373)
    ·
      refine ⟨41087929737790372696306945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219135625268215321046970373 41087929737790372696306945)
      ·
        refine ⟨30815947303342779522230209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41087929737790372696306945 30815947303342779522230209)
        ·
          refine ⟨23111960477507084641672657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30815947303342779522230209 23111960477507084641672657)
          ·
            refine ⟨17333970358130313481254493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23111960477507084641672657 17333970358130313481254493)
            ·
              refine ⟨6500238884298867555470435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17333970358130313481254493 6500238884298867555470435)
              ·
                refine ⟨9750358326448301333205653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6500238884298867555470435 9750358326448301333205653)
                ·
                  refine ⟨457048046552264124994015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9750358326448301333205653 457048046552264124994015)
                  ·
                    rfl

theorem cell23_8010881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 6].length) (baseStart_8010881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010881 prefixEnd_8010881 := by exact prefixLift 8010881
  have htrace : WordTrace (prefixWord ++ tailWord_8010881) baseStart_8010881 baseEnd_8010881 := by
    simpa [prefixWord, tailWord_8010881, baseEnd_8010881] using wordTrace_append hprefix tailTrace_8010881
  have hstable : (prefixWord ++ tailWord_8010881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010881).length < 2 ^ (prefixWord ++ tailWord_8010881).sum := by decide
  have hdescent : baseEnd_8010881 < baseStart_8010881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010925 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_8010925 : Nat := 118140960795 + 8010925 * 2 ^ 59
def prefixEnd_8010925 : Nat := 4983230072969 + 3 ^ 40 * 8010925 * 2
def baseEnd_8010925 : Nat := 4113455012119174952795933

theorem tailTrace_8010925 : CollatzResearch.WordTrace tailWord_8010925 prefixEnd_8010925 4113455012119174952795933 := by
  unfold tailWord_8010925
  simp only [CollatzResearch.WordTrace]
  refine ⟨292182438502794356910562229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194788292335196237940374819 292182438502794356910562229)
  ·
    refine ⟨27392103609636970960365209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292182438502794356910562229 27392103609636970960365209)
    ·
      refine ⟨20544077707227728220273907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27392103609636970960365209 20544077707227728220273907)
      ·
        refine ⟨30816116560841592330410861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20544077707227728220273907 30816116560841592330410861)
        ·
          refine ⟨11556043710315597123904073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30816116560841592330410861 11556043710315597123904073)
          ·
            refine ⟨8667032782736697842928055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11556043710315597123904073 8667032782736697842928055)
            ·
              refine ⟨13000549174105046764392083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8667032782736697842928055 13000549174105046764392083)
              ·
                refine ⟨19500823761157570146588125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13000549174105046764392083 19500823761157570146588125)
                ·
                  refine ⟨7312808910434088804970547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19500823761157570146588125 7312808910434088804970547)
                  ·
                    refine ⟨10969213365651133207455821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7312808910434088804970547 10969213365651133207455821)
                    ·
                      refine ⟨4113455012119174952795933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10969213365651133207455821 4113455012119174952795933)
                      ·
                        rfl

theorem cell23_8010925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_8010925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010925 prefixEnd_8010925 := by exact prefixLift 8010925
  have htrace : WordTrace (prefixWord ++ tailWord_8010925) baseStart_8010925 baseEnd_8010925 := by
    simpa [prefixWord, tailWord_8010925, baseEnd_8010925] using wordTrace_append hprefix tailTrace_8010925
  have hstable : (prefixWord ++ tailWord_8010925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010925).length < 2 ^ (prefixWord ++ tailWord_8010925).sum := by decide
  have hdescent : baseEnd_8010925 < baseStart_8010925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010927 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_8010927 : Nat := 118140960795 + 8010927 * 2 ^ 59
def prefixEnd_8010927 : Nat := 4983230072969 + 3 ^ 40 * 8010927 * 2
def baseEnd_8010927 : Nat := 4113456039080483944970923

theorem tailTrace_8010927 : CollatzResearch.WordTrace tailWord_8010927 prefixEnd_8010927 4113456039080483944970923 := by
  unfold tailWord_8010927
  simp only [CollatzResearch.WordTrace]
  refine ⟨292182511448787111252135035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194788340965858074168090023 292182511448787111252135035)
  ·
    refine ⟨438273767173180666878202553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292182511448787111252135035 438273767173180666878202553)
    ·
      refine ⟨328705325379885500158651915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438273767173180666878202553 328705325379885500158651915)
      ·
        refine ⟨493057988069828250237977873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328705325379885500158651915 493057988069828250237977873)
        ·
          refine ⟨369793491052371187678483405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493057988069828250237977873 369793491052371187678483405)
          ·
            refine ⟨138672559144639195379431277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369793491052371187678483405 138672559144639195379431277)
            ·
              refine ⟨52002209679239698267286729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138672559144639195379431277 52002209679239698267286729)
              ·
                refine ⟨39001657259429773700465047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52002209679239698267286729 39001657259429773700465047)
                ·
                  refine ⟨58502485889144660550697571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39001657259429773700465047 58502485889144660550697571)
                  ·
                    refine ⟨87753728833716990826046357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58502485889144660550697571 87753728833716990826046357)
                    ·
                      refine ⟨4113456039080483944970923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87753728833716990826046357 4113456039080483944970923)
                      ·
                        rfl

theorem cell23_8010927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_8010927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010927 prefixEnd_8010927 := by exact prefixLift 8010927
  have htrace : WordTrace (prefixWord ++ tailWord_8010927) baseStart_8010927 baseEnd_8010927 := by
    simpa [prefixWord, tailWord_8010927, baseEnd_8010927] using wordTrace_append hprefix tailTrace_8010927
  have hstable : (prefixWord ++ tailWord_8010927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010927).length < 2 ^ (prefixWord ++ tailWord_8010927).sum := by decide
  have hdescent : baseEnd_8010927 < baseStart_8010927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010937 : List Nat := [1, 2, 1, 4, 1, 3, 1, 10]
def baseStart_8010937 : Nat := 118140960795 + 8010937 * 2 ^ 59
def prefixEnd_8010937 : Nat := 4983230072969 + 3 ^ 40 * 8010937 * 2
def baseEnd_8010937 : Nat := 152350413847667737253551

theorem tailTrace_8010937 : CollatzResearch.WordTrace tailWord_8010937 prefixEnd_8010937 152350413847667737253551 := by
  unfold tailWord_8010937
  simp only [CollatzResearch.WordTrace]
  refine ⟨292182876178750882959999065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194788584119167255306666043 292182876178750882959999065)
  ·
    refine ⟨219137157134063162219999299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292182876178750882959999065 219137157134063162219999299)
    ·
      refine ⟨328705735701094743329998949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219137157134063162219999299 328705735701094743329998949)
      ·
        refine ⟨61632325443955264374374803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328705735701094743329998949 61632325443955264374374803)
        ·
          refine ⟨92448488165932896561562205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61632325443955264374374803 92448488165932896561562205)
          ·
            refine ⟨34668183062224836210585827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92448488165932896561562205 34668183062224836210585827)
            ·
              refine ⟨52002274593337254315878741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34668183062224836210585827 52002274593337254315878741)
              ·
                refine ⟨152350413847667737253551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52002274593337254315878741 152350413847667737253551)
                ·
                  rfl

theorem cell23_8010937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 10].length) (baseStart_8010937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010937 prefixEnd_8010937 := by exact prefixLift 8010937
  have htrace : WordTrace (prefixWord ++ tailWord_8010937) baseStart_8010937 baseEnd_8010937 := by
    simpa [prefixWord, tailWord_8010937, baseEnd_8010937] using wordTrace_append hprefix tailTrace_8010937
  have hstable : (prefixWord ++ tailWord_8010937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010937).length < 2 ^ (prefixWord ++ tailWord_8010937).sum := by decide
  have hdescent : baseEnd_8010937 < baseStart_8010937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8010968 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 1, 1, 5]
def baseStart_8010968 : Nat := 118140960795 + 8010968 * 2 ^ 59
def prefixEnd_8010968 : Nat := 4983230072969 + 3 ^ 40 * 8010968 * 2
def baseEnd_8010968 : Nat := 4113477091787318284558235

theorem tailTrace_8010968 : CollatzResearch.WordTrace tailWord_8010968 prefixEnd_8010968 4113477091787318284558235 := by
  unfold tailWord_8010968
  simp only [CollatzResearch.WordTrace]
  refine ⟨146092003420819287627188779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194789337894425716836251705 146092003420819287627188779)
  ·
    refine ⟨219138005131228931440783169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146092003420819287627188779 219138005131228931440783169)
    ·
      refine ⟨164353503848421698580587377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219138005131228931440783169 164353503848421698580587377)
      ·
        refine ⟨123265127886316273935440533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164353503848421698580587377 123265127886316273935440533)
        ·
          refine ⟨5778052869671075340723775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123265127886316273935440533 5778052869671075340723775)
          ·
            refine ⟨8667079304506613011085663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778052869671075340723775 8667079304506613011085663)
            ·
              refine ⟨13000618956759919516628495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8667079304506613011085663 13000618956759919516628495)
              ·
                refine ⟨19500928435139879274942743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13000618956759919516628495 19500928435139879274942743)
                ·
                  refine ⟨29251392652709818912414115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19500928435139879274942743 29251392652709818912414115)
                  ·
                    refine ⟨43877088979064728368621173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29251392652709818912414115 43877088979064728368621173)
                    ·
                      refine ⟨4113477091787318284558235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43877088979064728368621173 4113477091787318284558235)
                      ·
                        rfl

theorem cell23_8010968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_8010968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8010968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8010968 prefixEnd_8010968 := by exact prefixLift 8010968
  have htrace : WordTrace (prefixWord ++ tailWord_8010968) baseStart_8010968 baseEnd_8010968 := by
    simpa [prefixWord, tailWord_8010968, baseEnd_8010968] using wordTrace_append hprefix tailTrace_8010968
  have hstable : (prefixWord ++ tailWord_8010968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8010968).length < 2 ^ (prefixWord ++ tailWord_8010968).sum := by decide
  have hdescent : baseEnd_8010968 < baseStart_8010968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8010968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011121 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 3, 4]
def baseStart_8011121 : Nat := 118140960795 + 8011121 * 2 ^ 59
def prefixEnd_8011121 : Nat := 4983230072969 + 3 ^ 40 * 8011121 * 2
def baseEnd_8011121 : Nat := 1371185218109152061981677

theorem tailTrace_8011121 : CollatzResearch.WordTrace tailWord_8011121 prefixEnd_8011121 1371185218109152061981677 := by
  unfold tailWord_8011121
  simp only [CollatzResearch.WordTrace]
  refine ⟨292189587210084282384697217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194793058140056188256464811 292189587210084282384697217)
  ·
    refine ⟨219142190407563211788522913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292189587210084282384697217 219142190407563211788522913)
    ·
      refine ⟨164356642805672408841392185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219142190407563211788522913 164356642805672408841392185)
      ·
        refine ⟨123267482104254306631044139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164356642805672408841392185 123267482104254306631044139)
        ·
          refine ⟨184901223156381459946566209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123267482104254306631044139 184901223156381459946566209)
          ·
            refine ⟨138675917367286094959924657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184901223156381459946566209 138675917367286094959924657)
            ·
              refine ⟨104006938025464571219943493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138675917367286094959924657 104006938025464571219943493)
              ·
                refine ⟨19501300879774607103739405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104006938025464571219943493 19501300879774607103739405)
                ·
                  refine ⟨7312987829915477663902277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19501300879774607103739405 7312987829915477663902277)
                  ·
                    refine ⟨1371185218109152061981677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7312987829915477663902277 1371185218109152061981677)
                    ·
                      rfl

theorem cell23_8011121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_8011121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011121 prefixEnd_8011121 := by exact prefixLift 8011121
  have htrace : WordTrace (prefixWord ++ tailWord_8011121) baseStart_8011121 baseEnd_8011121 := by
    simpa [prefixWord, tailWord_8011121, baseEnd_8011121] using wordTrace_append hprefix tailTrace_8011121
  have hstable : (prefixWord ++ tailWord_8011121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011121).length < 2 ^ (prefixWord ++ tailWord_8011121).sum := by decide
  have hdescent : baseEnd_8011121 < baseStart_8011121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011212 : List Nat := [2, 2, 1, 4, 2, 1, 2, 4, 1, 1, 3]
def baseStart_8011212 : Nat := 118140960795 + 8011212 * 2 ^ 59
def prefixEnd_8011212 : Nat := 4983230072969 + 3 ^ 40 * 8011212 * 2
def baseEnd_8011212 : Nat := 4113602381067015329907113

theorem tailTrace_8011212 : CollatzResearch.WordTrace tailWord_8011212 prefixEnd_8011212 4113602381067015329907113 := by
  unfold tailWord_8011212
  simp only [CollatzResearch.WordTrace]
  refine ⟨146096453126377302463129945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194795270835169736617506593 146096453126377302463129945)
  ·
    refine ⟨109572339844782976847347459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146096453126377302463129945 109572339844782976847347459)
    ·
      refine ⟨164358509767174465271021189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109572339844782976847347459 164358509767174465271021189)
      ·
        refine ⟨30817220581345212238316473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164358509767174465271021189 30817220581345212238316473)
        ·
          refine ⟨23112915436008909178737355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30817220581345212238316473 23112915436008909178737355)
          ·
            refine ⟨34669373154013363768106033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23112915436008909178737355 34669373154013363768106033)
            ·
              refine ⟨26002029865510022826079525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34669373154013363768106033 26002029865510022826079525)
              ·
                refine ⟨4875380599783129279889911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26002029865510022826079525 4875380599783129279889911)
                ·
                  refine ⟨7313070899674693919834867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4875380599783129279889911 7313070899674693919834867)
                  ·
                    refine ⟨10969606349512040879752301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7313070899674693919834867 10969606349512040879752301)
                    ·
                      refine ⟨4113602381067015329907113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10969606349512040879752301 4113602381067015329907113)
                      ·
                        rfl

theorem cell23_8011212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_8011212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011212 prefixEnd_8011212 := by exact prefixLift 8011212
  have htrace : WordTrace (prefixWord ++ tailWord_8011212) baseStart_8011212 baseEnd_8011212 := by
    simpa [prefixWord, tailWord_8011212, baseEnd_8011212] using wordTrace_append hprefix tailTrace_8011212
  have hstable : (prefixWord ++ tailWord_8011212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011212).length < 2 ^ (prefixWord ++ tailWord_8011212).sum := by decide
  have hdescent : baseEnd_8011212 < baseStart_8011212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011231 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_8011231 : Nat := 118140960795 + 8011231 * 2 ^ 59
def prefixEnd_8011231 : Nat := 4983230072969 + 3 ^ 40 * 8011231 * 2
def baseEnd_8011231 : Nat := 4113612137199450755569525

theorem tailTrace_8011231 : CollatzResearch.WordTrace tailWord_8011231 prefixEnd_8011231 4113612137199450755569525 := by
  unfold tailWord_8011231
  simp only [CollatzResearch.WordTrace]
  refine ⟨292193599239685771171201547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194795732826457180780801031 292193599239685771171201547)
  ·
    refine ⟨438290398859528656756802321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292193599239685771171201547 438290398859528656756802321)
    ·
      refine ⟨328717799144646492567601741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438290398859528656756802321 328717799144646492567601741)
      ·
        refine ⟨123269174679242434712850653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328717799144646492567601741 123269174679242434712850653)
        ·
          refine ⟨46225940504715913017318995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123269174679242434712850653 46225940504715913017318995)
          ·
            refine ⟨69338910757073869525978493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46225940504715913017318995 69338910757073869525978493)
            ·
              refine ⟨26002091533902701072241935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69338910757073869525978493 26002091533902701072241935)
              ·
                refine ⟨39003137300854051608362903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26002091533902701072241935 39003137300854051608362903)
                ·
                  refine ⟨58504705951281077412544355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39003137300854051608362903 58504705951281077412544355)
                  ·
                    refine ⟨87757058926921616118816533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58504705951281077412544355 87757058926921616118816533)
                    ·
                      refine ⟨4113612137199450755569525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87757058926921616118816533 4113612137199450755569525)
                      ·
                        rfl

theorem cell23_8011231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_8011231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011231 prefixEnd_8011231 := by exact prefixLift 8011231
  have htrace : WordTrace (prefixWord ++ tailWord_8011231) baseStart_8011231 baseEnd_8011231 := by
    simpa [prefixWord, tailWord_8011231, baseEnd_8011231] using wordTrace_append hprefix tailTrace_8011231
  have hstable : (prefixWord ++ tailWord_8011231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011231).length < 2 ^ (prefixWord ++ tailWord_8011231).sum := by decide
  have hdescent : baseEnd_8011231 < baseStart_8011231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011235 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 4]
def baseStart_8011235 : Nat := 118140960795 + 8011235 * 2 ^ 59
def prefixEnd_8011235 : Nat := 4983230072969 + 3 ^ 40 * 8011235 * 2
def baseEnd_8011235 : Nat := 4113614191122068739919507

theorem tailTrace_8011235 : CollatzResearch.WordTrace tailWord_8011235 prefixEnd_8011235 4113614191122068739919507 := by
  unfold tailWord_8011235
  simp only [CollatzResearch.WordTrace]
  refine ⟨292193745131671279854347159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194795830087780853236231439 292193745131671279854347159)
  ·
    refine ⟨438290617697506919781520739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292193745131671279854347159 438290617697506919781520739)
    ·
      refine ⟨657435926546260379672281109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438290617697506919781520739 657435926546260379672281109)
      ·
        refine ⟨30817309056855955297138177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 657435926546260379672281109 30817309056855955297138177)
        ·
          refine ⟨23112981792641966472853633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30817309056855955297138177 23112981792641966472853633)
          ·
            refine ⟨17334736344481474854640225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23112981792641966472853633 17334736344481474854640225)
            ·
              refine ⟨13001052258361106140980169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17334736344481474854640225 13001052258361106140980169)
              ·
                refine ⟨9750789193770829605735127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13001052258361106140980169 9750789193770829605735127)
                ·
                  refine ⟨14626183790656244408602691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9750789193770829605735127 14626183790656244408602691)
                  ·
                    refine ⟨21939275685984366612904037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14626183790656244408602691 21939275685984366612904037)
                    ·
                      refine ⟨4113614191122068739919507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21939275685984366612904037 4113614191122068739919507)
                      ·
                        rfl

theorem cell23_8011235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_8011235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011235 prefixEnd_8011235 := by exact prefixLift 8011235
  have htrace : WordTrace (prefixWord ++ tailWord_8011235) baseStart_8011235 baseEnd_8011235 := by
    simpa [prefixWord, tailWord_8011235, baseEnd_8011235] using wordTrace_append hprefix tailTrace_8011235
  have hstable : (prefixWord ++ tailWord_8011235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011235).length < 2 ^ (prefixWord ++ tailWord_8011235).sum := by decide
  have hdescent : baseEnd_8011235 < baseStart_8011235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011301 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_8011301 : Nat := 118140960795 + 8011301 * 2 ^ 59
def prefixEnd_8011301 : Nat := 4983230072969 + 3 ^ 40 * 8011301 * 2
def baseEnd_8011301 : Nat := 1371216026948421827231401

theorem tailTrace_8011301 : CollatzResearch.WordTrace tailWord_8011301 prefixEnd_8011301 1371216026948421827231401 := by
  unfold tailWord_8011301
  simp only [CollatzResearch.WordTrace]
  refine ⟨292196152349432173126249757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194797434899621448750833171 292196152349432173126249757)
  ·
    refine ⟨109573557131037064922343659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292196152349432173126249757 109573557131037064922343659)
    ·
      refine ⟨164360335696555597383515489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109573557131037064922343659 164360335696555597383515489)
      ·
        refine ⟨123270251772416698037636617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164360335696555597383515489 123270251772416698037636617)
        ·
          refine ⟨92452688829312523528227463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123270251772416698037636617 92452688829312523528227463)
          ·
            refine ⟨138679033243968785292341195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92452688829312523528227463 138679033243968785292341195)
            ·
              refine ⟨208018549865953177938511793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138679033243968785292341195 208018549865953177938511793)
              ·
                refine ⟨156013912399464883453883845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208018549865953177938511793 156013912399464883453883845)
                ·
                  refine ⟨29252608574899665647603221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156013912399464883453883845 29252608574899665647603221)
                  ·
                    refine ⟨1371216026948421827231401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29252608574899665647603221 1371216026948421827231401)
                    ·
                      rfl

theorem cell23_8011301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_8011301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011301 prefixEnd_8011301 := by exact prefixLift 8011301
  have htrace : WordTrace (prefixWord ++ tailWord_8011301) baseStart_8011301 baseEnd_8011301 := by
    simpa [prefixWord, tailWord_8011301, baseEnd_8011301] using wordTrace_append hprefix tailTrace_8011301
  have hstable : (prefixWord ++ tailWord_8011301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011301).length < 2 ^ (prefixWord ++ tailWord_8011301).sum := by decide
  have hdescent : baseEnd_8011301 < baseStart_8011301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011338 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_8011338 : Nat := 118140960795 + 8011338 * 2 ^ 59
def prefixEnd_8011338 : Nat := 4983230072969 + 3 ^ 40 * 8011338 * 2
def baseEnd_8011338 : Nat := 4113667079629481836931533

theorem tailTrace_8011338 : CollatzResearch.WordTrace tailWord_8011338 prefixEnd_8011338 4113667079629481836931533 := by
  unfold tailWord_8011338
  simp only [CollatzResearch.WordTrace]
  refine ⟨73049375462574532111336667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194798334566865418963564445 73049375462574532111336667)
  ·
    refine ⟨109574063193861798167005001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73049375462574532111336667 109574063193861798167005001)
    ·
      refine ⟨82180547395396348625253751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109574063193861798167005001 82180547395396348625253751)
      ·
        refine ⟨123270821093094522937880627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82180547395396348625253751 123270821093094522937880627)
        ·
          refine ⟨184906231639641784406820941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123270821093094522937880627 184906231639641784406820941)
          ·
            refine ⟨69339836864865669152557853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184906231639641784406820941 69339836864865669152557853)
            ·
              refine ⟨26002438824324625932209195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69339836864865669152557853 26002438824324625932209195)
              ·
                refine ⟨39003658236486938898313793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26002438824324625932209195 39003658236486938898313793)
                ·
                  refine ⟨29252743677365204173735345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39003658236486938898313793 29252743677365204173735345)
                  ·
                    refine ⟨21939557758023903130301509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29252743677365204173735345 21939557758023903130301509)
                    ·
                      refine ⟨4113667079629481836931533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21939557758023903130301509 4113667079629481836931533)
                      ·
                        rfl

theorem cell23_8011338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_8011338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011338 prefixEnd_8011338 := by exact prefixLift 8011338
  have htrace : WordTrace (prefixWord ++ tailWord_8011338) baseStart_8011338 baseEnd_8011338 := by
    simpa [prefixWord, tailWord_8011338, baseEnd_8011338] using wordTrace_append hprefix tailTrace_8011338
  have hstable : (prefixWord ++ tailWord_8011338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011338).length < 2 ^ (prefixWord ++ tailWord_8011338).sum := by decide
  have hdescent : baseEnd_8011338 < baseStart_8011338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011348 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 7]
def baseStart_8011348 : Nat := 118140960795 + 8011348 * 2 ^ 59
def prefixEnd_8011348 : Nat := 4983230072969 + 3 ^ 40 * 8011348 * 2
def baseEnd_8011348 : Nat := 457074690492891866422943

theorem tailTrace_8011348 : CollatzResearch.WordTrace tailWord_8011348 prefixEnd_8011348 457074690492891866422943 := by
  unfold tailWord_8011348
  simp only [CollatzResearch.WordTrace]
  refine ⟨146098933290130950076605349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194798577720174600102140465 146098933290130950076605349)
  ·
    refine ⟨27393549991899553139363503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146098933290130950076605349 27393549991899553139363503)
    ·
      refine ⟨41090324987849329709045255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27393549991899553139363503 41090324987849329709045255)
      ·
        refine ⟨61635487481773994563567883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41090324987849329709045255 61635487481773994563567883)
        ·
          refine ⟨92453231222660991845351825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61635487481773994563567883 92453231222660991845351825)
          ·
            refine ⟨69339923416995743884013869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92453231222660991845351825 69339923416995743884013869)
            ·
              refine ⟨26002471281373403956505201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69339923416995743884013869 26002471281373403956505201)
              ·
                refine ⟨19501853461030052967378901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26002471281373403956505201 19501853461030052967378901)
                ·
                  refine ⟨457074690492891866422943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19501853461030052967378901 457074690492891866422943)
                  ·
                    rfl

theorem cell23_8011348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_8011348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011348 prefixEnd_8011348 := by exact prefixLift 8011348
  have htrace : WordTrace (prefixWord ++ tailWord_8011348) baseStart_8011348 baseEnd_8011348 := by
    simpa [prefixWord, tailWord_8011348, baseEnd_8011348] using wordTrace_append hprefix tailTrace_8011348
  have hstable : (prefixWord ++ tailWord_8011348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011348).length < 2 ^ (prefixWord ++ tailWord_8011348).sum := by decide
  have hdescent : baseEnd_8011348 < baseStart_8011348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011365 : List Nat := [1, 3, 1, 3, 3, 1, 1, 5, 5]
def baseStart_8011365 : Nat := 118140960795 + 8011365 * 2 ^ 59
def prefixEnd_8011365 : Nat := 4983230072969 + 3 ^ 40 * 8011365 * 2
def baseEnd_8011365 : Nat := 457075660400794803477101

theorem tailTrace_8011365 : CollatzResearch.WordTrace tailWord_8011365 prefixEnd_8011365 457075660400794803477101 := by
  unfold tailWord_8011365
  simp only [CollatzResearch.WordTrace]
  refine ⟨292198486621200312056579549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194798991080800208037719699 292198486621200312056579549)
  ·
    refine ⟨109574432482950117021217331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292198486621200312056579549 109574432482950117021217331)
    ·
      refine ⟨164361648724425175531825997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109574432482950117021217331 164361648724425175531825997)
      ·
        refine ⟨61635618271659440824434749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164361648724425175531825997 61635618271659440824434749)
        ·
          refine ⟨23113356851872290309163031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61635618271659440824434749 23113356851872290309163031)
          ·
            refine ⟨34670035277808435463744547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23113356851872290309163031 34670035277808435463744547)
            ·
              refine ⟨52005052916712653195616821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34670035277808435463744547 52005052916712653195616821)
              ·
                refine ⟨4875473710941811237089077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52005052916712653195616821 4875473710941811237089077)
                ·
                  refine ⟨457075660400794803477101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4875473710941811237089077 457075660400794803477101)
                  ·
                    rfl

theorem cell23_8011365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_8011365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011365 prefixEnd_8011365 := by exact prefixLift 8011365
  have htrace : WordTrace (prefixWord ++ tailWord_8011365) baseStart_8011365 baseEnd_8011365 := by
    simpa [prefixWord, tailWord_8011365, baseEnd_8011365] using wordTrace_append hprefix tailTrace_8011365
  have hstable : (prefixWord ++ tailWord_8011365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011365).length < 2 ^ (prefixWord ++ tailWord_8011365).sum := by decide
  have hdescent : baseEnd_8011365 < baseStart_8011365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011382 : List Nat := [5, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_8011382 : Nat := 118140960795 + 8011382 * 2 ^ 59
def prefixEnd_8011382 : Nat := 4983230072969 + 3 ^ 40 * 8011382 * 2
def baseEnd_8011382 : Nat := 457076630308697740531259

theorem tailTrace_8011382 : CollatzResearch.WordTrace tailWord_8011382 prefixEnd_8011382 457076630308697740531259 := by
  unfold tailWord_8011382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18262444166383670247496775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 194799404441425815973298933 18262444166383670247496775)
  ·
    refine ⟨27393666249575505371245163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18262444166383670247496775 27393666249575505371245163)
    ·
      refine ⟨41090499374363258056867745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27393666249575505371245163 41090499374363258056867745)
      ·
        refine ⟨30817874530772443542650809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41090499374363258056867745 30817874530772443542650809)
        ·
          refine ⟨23113405898079332656988107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30817874530772443542650809 23113405898079332656988107)
          ·
            refine ⟨34670108847118998985482161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23113405898079332656988107 34670108847118998985482161)
            ·
              refine ⟨26002581635339249239111621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34670108847118998985482161 26002581635339249239111621)
              ·
                refine ⟨4875484056626109232333429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26002581635339249239111621 4875484056626109232333429)
                ·
                  refine ⟨457076630308697740531259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4875484056626109232333429 457076630308697740531259)
                  ·
                    rfl

theorem cell23_8011382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_8011382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011382 prefixEnd_8011382 := by exact prefixLift 8011382
  have htrace : WordTrace (prefixWord ++ tailWord_8011382) baseStart_8011382 baseEnd_8011382 := by
    simpa [prefixWord, tailWord_8011382, baseEnd_8011382] using wordTrace_append hprefix tailTrace_8011382
  have hstable : (prefixWord ++ tailWord_8011382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011382).length < 2 ^ (prefixWord ++ tailWord_8011382).sum := by decide
  have hdescent : baseEnd_8011382 < baseStart_8011382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011442 : List Nat := [3, 2, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_8011442 : Nat := 118140960795 + 8011442 * 2 ^ 59
def prefixEnd_8011442 : Nat := 4983230072969 + 3 ^ 40 * 8011442 * 2
def baseEnd_8011442 : Nat := 1371240160539183143343685

theorem tailTrace_8011442 : CollatzResearch.WordTrace tailWord_8011442 prefixEnd_8011442 1371240160539183143343685 := by
  unfold tailWord_8011442
  simp only [CollatzResearch.WordTrace]
  refine ⟨73050323760480338551783145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194800863361280902804755053 73050323760480338551783145)
  ·
    refine ⟨54787742820360253913837359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73050323760480338551783145 54787742820360253913837359)
    ·
      refine ⟨82181614230540380870756039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54787742820360253913837359 82181614230540380870756039)
      ·
        refine ⟨123272421345810571306134059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82181614230540380870756039 123272421345810571306134059)
        ·
          refine ⟨184908632018715856959201089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123272421345810571306134059 184908632018715856959201089)
          ·
            refine ⟨138681474014036892719400817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184908632018715856959201089 138681474014036892719400817)
            ·
              refine ⟨104011105510527669539550613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138681474014036892719400817 104011105510527669539550613)
              ·
                refine ⟨4875520570805984509666435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104011105510527669539550613 4875520570805984509666435)
                ·
                  refine ⟨7313280856208976764499653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4875520570805984509666435 7313280856208976764499653)
                  ·
                    refine ⟨1371240160539183143343685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7313280856208976764499653 1371240160539183143343685)
                    ·
                      rfl

theorem cell23_8011442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_8011442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011442 prefixEnd_8011442 := by exact prefixLift 8011442
  have htrace : WordTrace (prefixWord ++ tailWord_8011442) baseStart_8011442 baseEnd_8011442 := by
    simpa [prefixWord, tailWord_8011442, baseEnd_8011442] using wordTrace_append hprefix tailTrace_8011442
  have hstable : (prefixWord ++ tailWord_8011442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011442).length < 2 ^ (prefixWord ++ tailWord_8011442).sum := by decide
  have hdescent : baseEnd_8011442 < baseStart_8011442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011469 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_8011469 : Nat := 118140960795 + 8011469 * 2 ^ 59
def prefixEnd_8011469 : Nat := 4983230072969 + 3 ^ 40 * 8011469 * 2
def baseEnd_8011469 : Nat := 4113734345595220824393431

theorem tailTrace_8011469 : CollatzResearch.WordTrace tailWord_8011469 prefixEnd_8011469 4113734345595220824393431 := by
  unfold tailWord_8011469
  simp only [CollatzResearch.WordTrace]
  refine ⟨292202279812823537818365461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194801519875215691878910307 292202279812823537818365461)
  ·
    refine ⟨13696981866226103335235881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 292202279812823537818365461 13696981866226103335235881)
    ·
      refine ⟨10272736399669577501426911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13696981866226103335235881 10272736399669577501426911)
      ·
        refine ⟨15409104599504366252140367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10272736399669577501426911 15409104599504366252140367)
        ·
          refine ⟨23113656899256549378210551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15409104599504366252140367 23113656899256549378210551)
          ·
            refine ⟨34670485348884824067315827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23113656899256549378210551 34670485348884824067315827)
            ·
              refine ⟨52005728023327236100973741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34670485348884824067315827 52005728023327236100973741)
              ·
                refine ⟨19502148008747713537865153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52005728023327236100973741 19502148008747713537865153)
                ·
                  refine ⟨14626611006560785153398865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19502148008747713537865153 14626611006560785153398865)
                  ·
                    refine ⟨10969958254920588865049149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14626611006560785153398865 10969958254920588865049149)
                    ·
                      refine ⟨4113734345595220824393431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10969958254920588865049149 4113734345595220824393431)
                      ·
                        rfl

theorem cell23_8011469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_8011469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011469 prefixEnd_8011469 := by exact prefixLift 8011469
  have htrace : WordTrace (prefixWord ++ tailWord_8011469) baseStart_8011469 baseEnd_8011469 := by
    simpa [prefixWord, tailWord_8011469, baseEnd_8011469] using wordTrace_append hprefix tailTrace_8011469
  have hstable : (prefixWord ++ tailWord_8011469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011469).length < 2 ^ (prefixWord ++ tailWord_8011469).sum := by decide
  have hdescent : baseEnd_8011469 < baseStart_8011469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011492 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 2, 3, 2]
def baseStart_8011492 : Nat := 118140960795 + 8011492 * 2 ^ 59
def prefixEnd_8011492 : Nat := 4983230072969 + 3 ^ 40 * 8011492 * 2
def baseEnd_8011492 : Nat := 4113746155650274234405825

theorem tailTrace_8011492 : CollatzResearch.WordTrace tailWord_8011492 prefixEnd_8011492 4113746155650274234405825 := by
  unfold tailWord_8011492
  simp only [CollatzResearch.WordTrace]
  refine ⟨146101559345870106373226365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194802079127826808497635153 146101559345870106373226365)
  ·
    refine ⟨54788084754701289889959887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146101559345870106373226365 54788084754701289889959887)
    ·
      refine ⟨82182127132051934834939831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54788084754701289889959887 82182127132051934834939831)
      ·
        refine ⟨123273190698077902252409747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82182127132051934834939831 123273190698077902252409747)
        ·
          refine ⟨184909786047116853378614621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123273190698077902252409747 184909786047116853378614621)
          ·
            refine ⟨69341169767668820016980483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184909786047116853378614621 69341169767668820016980483)
            ·
              refine ⟨104011754651503230025470725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69341169767668820016980483 104011754651503230025470725)
              ·
                refine ⟨19502203997156855629775761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104011754651503230025470725 19502203997156855629775761)
                ·
                  refine ⟨14626652997867641722331821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19502203997156855629775761 14626652997867641722331821)
                  ·
                    refine ⟨5484994874200365645874433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14626652997867641722331821 5484994874200365645874433)
                    ·
                      refine ⟨4113746155650274234405825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5484994874200365645874433 4113746155650274234405825)
                      ·
                        rfl

theorem cell23_8011492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_8011492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011492 prefixEnd_8011492 := by exact prefixLift 8011492
  have htrace : WordTrace (prefixWord ++ tailWord_8011492) baseStart_8011492 baseEnd_8011492 := by
    simpa [prefixWord, tailWord_8011492, baseEnd_8011492] using wordTrace_append hprefix tailTrace_8011492
  have hstable : (prefixWord ++ tailWord_8011492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011492).length < 2 ^ (prefixWord ++ tailWord_8011492).sum := by decide
  have hdescent : baseEnd_8011492 < baseStart_8011492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011505 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_8011505 : Nat := 118140960795 + 8011505 * 2 ^ 59
def prefixEnd_8011505 : Nat := 4983230072969 + 3 ^ 40 * 8011505 * 2
def baseEnd_8011505 : Nat := 4113752830898782683543265

theorem tailTrace_8011505 : CollatzResearch.WordTrace tailWord_8011505 prefixEnd_8011505 4113752830898782683543265 := by
  unfold tailWord_8011505
  simp only [CollatzResearch.WordTrace]
  refine ⟨292203592840693115966675969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194802395227128743977783979 292203592840693115966675969)
  ·
    refine ⟨219152694630519836975006977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292203592840693115966675969 219152694630519836975006977)
    ·
      refine ⟨164364520972889877731255233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219152694630519836975006977 164364520972889877731255233)
      ·
        refine ⟨123273390729667408298441425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164364520972889877731255233 123273390729667408298441425)
        ·
          refine ⟨92455043047250556223831069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123273390729667408298441425 92455043047250556223831069)
          ·
            refine ⟨34670641142718958583936651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92455043047250556223831069 34670641142718958583936651)
            ·
              refine ⟨52005961714078437875904977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34670641142718958583936651 52005961714078437875904977)
              ·
                refine ⟨39004471285558828406928733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52005961714078437875904977 39004471285558828406928733)
                ·
                  refine ⟨14626676732084560652598275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39004471285558828406928733 14626676732084560652598275)
                  ·
                    refine ⟨21940015098126840978897413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14626676732084560652598275 21940015098126840978897413)
                    ·
                      refine ⟨4113752830898782683543265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21940015098126840978897413 4113752830898782683543265)
                      ·
                        rfl

theorem cell23_8011505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_8011505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011505 prefixEnd_8011505 := by exact prefixLift 8011505
  have htrace : WordTrace (prefixWord ++ tailWord_8011505) baseStart_8011505 baseEnd_8011505 := by
    simpa [prefixWord, tailWord_8011505, baseEnd_8011505] using wordTrace_append hprefix tailTrace_8011505
  have hstable : (prefixWord ++ tailWord_8011505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011505).length < 2 ^ (prefixWord ++ tailWord_8011505).sum := by decide
  have hdescent : baseEnd_8011505 < baseStart_8011505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011522 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_8011522 : Nat := 118140960795 + 8011522 * 2 ^ 59
def prefixEnd_8011522 : Nat := 4983230072969 + 3 ^ 40 * 8011522 * 2
def baseEnd_8011522 : Nat := 4113761560069909117030687

theorem tailTrace_8011522 : CollatzResearch.WordTrace tailWord_8011522 prefixEnd_8011522 4113761560069909117030687 := by
  unfold tailWord_8011522
  simp only [CollatzResearch.WordTrace]
  refine ⟨73051053220407881967511205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194802808587754351913363213 73051053220407881967511205)
  ·
    refine ⟨13697072478826477868908351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73051053220407881967511205 13697072478826477868908351)
    ·
      refine ⟨20545608718239716803362527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13697072478826477868908351 20545608718239716803362527)
      ·
        refine ⟨30818413077359575205043791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20545608718239716803362527 30818413077359575205043791)
        ·
          refine ⟨46227619616039362807565687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30818413077359575205043791 46227619616039362807565687)
          ·
            refine ⟨69341429424059044211348531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46227619616039362807565687 69341429424059044211348531)
            ·
              refine ⟨104012144136088566317022797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69341429424059044211348531 104012144136088566317022797)
              ·
                refine ⟨39004554051033212368883549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104012144136088566317022797 39004554051033212368883549)
                ·
                  refine ⟨14626707769137454638331331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39004554051033212368883549 14626707769137454638331331)
                  ·
                    refine ⟨21940061653706181957496997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14626707769137454638331331 21940061653706181957496997)
                    ·
                      refine ⟨4113761560069909117030687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21940061653706181957496997 4113761560069909117030687)
                      ·
                        rfl

theorem cell23_8011522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_8011522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011522 prefixEnd_8011522 := by exact prefixLift 8011522
  have htrace : WordTrace (prefixWord ++ tailWord_8011522) baseStart_8011522 baseEnd_8011522 := by
    simpa [prefixWord, tailWord_8011522, baseEnd_8011522] using wordTrace_append hprefix tailTrace_8011522
  have hstable : (prefixWord ++ tailWord_8011522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011522).length < 2 ^ (prefixWord ++ tailWord_8011522).sum := by decide
  have hdescent : baseEnd_8011522 < baseStart_8011522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011555 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 3]
def baseStart_8011555 : Nat := 118140960795 + 8011555 * 2 ^ 59
def prefixEnd_8011555 : Nat := 4983230072969 + 3 ^ 40 * 8011555 * 2
def baseEnd_8011555 : Nat := 4113778504931507487918035

theorem tailTrace_8011555 : CollatzResearch.WordTrace tailWord_8011555 prefixEnd_8011555 4113778504931507487918035 := by
  unfold tailWord_8011555
  simp only [CollatzResearch.WordTrace]
  refine ⟨292205416490511974505996119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194803610993674649670664079 292205416490511974505996119)
  ·
    refine ⟨438308124735767961758994179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292205416490511974505996119 438308124735767961758994179)
    ·
      refine ⟨657462187103651942638491269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438308124735767961758994179 657462187103651942638491269)
      ·
        refine ⟨123274160081934739244717113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 657462187103651942638491269 123274160081934739244717113)
        ·
          refine ⟨92455620061451054433537835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123274160081934739244717113 92455620061451054433537835)
          ·
            refine ⟨138683430092176581650306753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92455620061451054433537835 138683430092176581650306753)
            ·
              refine ⟨104012572569132436237730065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138683430092176581650306753 104012572569132436237730065)
              ·
                refine ⟨78009429426849327178297549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104012572569132436237730065 78009429426849327178297549)
                ·
                  refine ⟨29253536035068497691861581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78009429426849327178297549 29253536035068497691861581)
                  ·
                    refine ⟨10970076013150686634448093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29253536035068497691861581 10970076013150686634448093)
                    ·
                      refine ⟨4113778504931507487918035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10970076013150686634448093 4113778504931507487918035)
                      ·
                        rfl

theorem cell23_8011555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_8011555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011555 prefixEnd_8011555 := by exact prefixLift 8011555
  have htrace : WordTrace (prefixWord ++ tailWord_8011555) baseStart_8011555 baseEnd_8011555 := by
    simpa [prefixWord, tailWord_8011555, baseEnd_8011555] using wordTrace_append hprefix tailTrace_8011555
  have hstable : (prefixWord ++ tailWord_8011555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011555).length < 2 ^ (prefixWord ++ tailWord_8011555).sum := by decide
  have hdescent : baseEnd_8011555 < baseStart_8011555 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011556 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 3, 2, 2]
def baseStart_8011556 : Nat := 118140960795 + 8011556 * 2 ^ 59
def prefixEnd_8011556 : Nat := 4983230072969 + 3 ^ 40 * 8011556 * 2
def baseEnd_8011556 : Nat := 4113779018412161984005531

theorem tailTrace_8011556 : CollatzResearch.WordTrace tailWord_8011556 prefixEnd_8011556 4113779018412161984005531 := by
  unfold tailWord_8011556
  simp only [CollatzResearch.WordTrace]
  refine ⟨146102726481754175838391261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194803635309005567784521681 146102726481754175838391261)
  ·
    refine ⟨54788522430657815939396723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146102726481754175838391261 54788522430657815939396723)
    ·
      refine ⟨82182783645986723909095085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54788522430657815939396723 82182783645986723909095085)
      ·
        refine ⟨30818543867245021465910657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82182783645986723909095085 30818543867245021465910657)
        ·
          refine ⟨23113907900433766099432993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30818543867245021465910657 23113907900433766099432993)
          ·
            refine ⟨17335430925325324574574745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23113907900433766099432993 17335430925325324574574745)
            ·
              refine ⟨13001573193993993430931059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17335430925325324574574745 13001573193993993430931059)
              ·
                refine ⟨19502359790990990146396589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13001573193993993430931059 19502359790990990146396589)
                ·
                  refine ⟨7313384921621621304898721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19502359790990990146396589 7313384921621621304898721)
                  ·
                    refine ⟨5485038691216215978674041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7313384921621621304898721 5485038691216215978674041)
                    ·
                      refine ⟨4113779018412161984005531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485038691216215978674041 4113779018412161984005531)
                      ·
                        rfl

theorem cell23_8011556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_8011556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011556 prefixEnd_8011556 := by exact prefixLift 8011556
  have htrace : WordTrace (prefixWord ++ tailWord_8011556) baseStart_8011556 baseEnd_8011556 := by
    simpa [prefixWord, tailWord_8011556, baseEnd_8011556] using wordTrace_append hprefix tailTrace_8011556
  have hstable : (prefixWord ++ tailWord_8011556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011556).length < 2 ^ (prefixWord ++ tailWord_8011556).sum := by decide
  have hdescent : baseEnd_8011556 < baseStart_8011556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011566 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_8011566 : Nat := 118140960795 + 8011566 * 2 ^ 59
def prefixEnd_8011566 : Nat := 4983230072969 + 3 ^ 40 * 8011566 * 2
def baseEnd_8011566 : Nat := 1371261384406235648293495

theorem tailTrace_8011566 : CollatzResearch.WordTrace tailWord_8011566 prefixEnd_8011566 1371261384406235648293495 := by
  unfold tailWord_8011566
  simp only [CollatzResearch.WordTrace]
  refine ⟨36525727211684015423080819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194803878462314748923097701 36525727211684015423080819)
  ·
    refine ⟨54788590817526023134621229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36525727211684015423080819 54788590817526023134621229)
    ·
      refine ⟨20545721556572258675482961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54788590817526023134621229 20545721556572258675482961)
      ·
        refine ⟨15409291167429194006612221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20545721556572258675482961 15409291167429194006612221)
        ·
          refine ⟨5778484187785947752479583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15409291167429194006612221 5778484187785947752479583)
          ·
            refine ⟨8667726281678921628719375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778484187785947752479583 8667726281678921628719375)
            ·
              refine ⟨13001589422518382443079063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8667726281678921628719375 13001589422518382443079063)
              ·
                refine ⟨19502384133777573664618595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13001589422518382443079063 19502384133777573664618595)
                ·
                  refine ⟨29253576200666360496927893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19502384133777573664618595 29253576200666360496927893)
                  ·
                    refine ⟨1371261384406235648293495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29253576200666360496927893 1371261384406235648293495)
                    ·
                      rfl

theorem cell23_8011566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_8011566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011566 prefixEnd_8011566 := by exact prefixLift 8011566
  have htrace : WordTrace (prefixWord ++ tailWord_8011566) baseStart_8011566 baseEnd_8011566 := by
    simpa [prefixWord, tailWord_8011566, baseEnd_8011566] using wordTrace_append hprefix tailTrace_8011566
  have hstable : (prefixWord ++ tailWord_8011566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011566).length < 2 ^ (prefixWord ++ tailWord_8011566).sum := by decide
  have hdescent : baseEnd_8011566 < baseStart_8011566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011625 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_8011625 : Nat := 118140960795 + 8011625 * 2 ^ 59
def prefixEnd_8011625 : Nat := 4983230072969 + 3 ^ 40 * 8011625 * 2
def baseEnd_8011625 : Nat := 4113814448577322214042713

theorem tailTrace_8011625 : CollatzResearch.WordTrace tailWord_8011625 prefixEnd_8011625 4113814448577322214042713 := by
  unfold tailWord_8011625
  simp only [CollatzResearch.WordTrace]
  refine ⟨292207969600258376461044329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194805313066838917640696219 292207969600258376461044329)
  ·
    refine ⟨219155977200193782345783247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292207969600258376461044329 219155977200193782345783247)
    ·
      refine ⟨328733965800290673518674871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219155977200193782345783247 328733965800290673518674871)
      ·
        refine ⟨493100948700436010278012307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328733965800290673518674871 493100948700436010278012307)
        ·
          refine ⟨739651423050654015417018461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493100948700436010278012307 739651423050654015417018461)
          ·
            refine ⟨277369283643995255781381923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 739651423050654015417018461 277369283643995255781381923)
            ·
              refine ⟨416053925465992883672072885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277369283643995255781381923 416053925465992883672072885)
              ·
                refine ⟨39005055512436832844256833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 416053925465992883672072885 39005055512436832844256833)
                ·
                  refine ⟨29253791634327624633192625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39005055512436832844256833 29253791634327624633192625)
                  ·
                    refine ⟨21940343725745718474894469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29253791634327624633192625 21940343725745718474894469)
                    ·
                      refine ⟨4113814448577322214042713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21940343725745718474894469 4113814448577322214042713)
                      ·
                        rfl

theorem cell23_8011625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_8011625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011625 prefixEnd_8011625 := by exact prefixLift 8011625
  have htrace : WordTrace (prefixWord ++ tailWord_8011625) baseStart_8011625 baseEnd_8011625 := by
    simpa [prefixWord, tailWord_8011625, baseEnd_8011625] using wordTrace_append hprefix tailTrace_8011625
  have hstable : (prefixWord ++ tailWord_8011625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011625).length < 2 ^ (prefixWord ++ tailWord_8011625).sum := by decide
  have hdescent : baseEnd_8011625 < baseStart_8011625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011646 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_8011646 : Nat := 118140960795 + 8011646 * 2 ^ 59
def prefixEnd_8011646 : Nat := 4983230072969 + 3 ^ 40 * 8011646 * 2
def baseEnd_8011646 : Nat := 4113825231671066631880117

theorem tailTrace_8011646 : CollatzResearch.WordTrace tailWord_8011646 prefixEnd_8011646 4113825231671066631880117 := by
  unfold tailWord_8011646
  simp only [CollatzResearch.WordTrace]
  refine ⟨36526091941647787130944849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194805823688788198031705861 36526091941647787130944849)
  ·
    refine ⟨27394568956235840348208637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36526091941647787130944849 27394568956235840348208637)
    ·
      refine ⟨10272963358588440130578239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27394568956235840348208637 10272963358588440130578239)
      ·
        refine ⟨15409445037882660195867359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10272963358588440130578239 15409445037882660195867359)
        ·
          refine ⟨23114167556823990293801039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15409445037882660195867359 23114167556823990293801039)
          ·
            refine ⟨34671251335235985440701559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23114167556823990293801039 34671251335235985440701559)
            ·
              refine ⟨52006877002853978161052339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34671251335235985440701559 52006877002853978161052339)
              ·
                refine ⟨78010315504280967241578509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52006877002853978161052339 78010315504280967241578509)
                ·
                  refine ⟨29253868314105362715591941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78010315504280967241578509 29253868314105362715591941)
                  ·
                    refine ⟨5485100308894755509173489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29253868314105362715591941 5485100308894755509173489)
                    ·
                      refine ⟨4113825231671066631880117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485100308894755509173489 4113825231671066631880117)
                      ·
                        rfl

theorem cell23_8011646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_8011646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011646 prefixEnd_8011646 := by exact prefixLift 8011646
  have htrace : WordTrace (prefixWord ++ tailWord_8011646) baseStart_8011646 baseEnd_8011646 := by
    simpa [prefixWord, tailWord_8011646, baseEnd_8011646] using wordTrace_append hprefix tailTrace_8011646
  have hstable : (prefixWord ++ tailWord_8011646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011646).length < 2 ^ (prefixWord ++ tailWord_8011646).sum := by decide
  have hdescent : baseEnd_8011646 < baseStart_8011646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011679 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 3]
def baseStart_8011679 : Nat := 118140960795 + 8011679 * 2 ^ 59
def prefixEnd_8011679 : Nat := 4983230072969 + 3 ^ 40 * 8011679 * 2
def baseEnd_8011679 : Nat := 4113842176532665002767465

theorem tailTrace_8011679 : CollatzResearch.WordTrace tailWord_8011679 prefixEnd_8011679 4113842176532665002767465 := by
  unfold tailWord_8011679
  simp only [CollatzResearch.WordTrace]
  refine ⟨292209939142062743683510091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194806626094708495789006727 292209939142062743683510091)
  ·
    refine ⟨438314908713094115525265137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292209939142062743683510091 438314908713094115525265137)
    ·
      refine ⟨328736181534820586643948853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438314908713094115525265137 328736181534820586643948853)
      ·
        refine ⟨30819017018889429997870205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 328736181534820586643948853 30819017018889429997870205)
        ·
          refine ⟨11557131382083536249201327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30819017018889429997870205 11557131382083536249201327)
          ·
            refine ⟨17335697073125304373801991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11557131382083536249201327 17335697073125304373801991)
            ·
              refine ⟨26003545609687956560702987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17335697073125304373801991 26003545609687956560702987)
              ·
                refine ⟨39005318414531934841054481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26003545609687956560702987 39005318414531934841054481)
                ·
                  refine ⟨29253988810898951130790861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39005318414531934841054481 29253988810898951130790861)
                  ·
                    refine ⟨10970245804087106674046573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29253988810898951130790861 10970245804087106674046573)
                    ·
                      refine ⟨4113842176532665002767465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10970245804087106674046573 4113842176532665002767465)
                      ·
                        rfl

theorem cell23_8011679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_8011679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011679 prefixEnd_8011679 := by exact prefixLift 8011679
  have htrace : WordTrace (prefixWord ++ tailWord_8011679) baseStart_8011679 baseEnd_8011679 := by
    simpa [prefixWord, tailWord_8011679, baseEnd_8011679] using wordTrace_append hprefix tailTrace_8011679
  have hstable : (prefixWord ++ tailWord_8011679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011679).length < 2 ^ (prefixWord ++ tailWord_8011679).sum := by decide
  have hdescent : baseEnd_8011679 < baseStart_8011679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011712 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 5, 4]
def baseStart_8011712 : Nat := 118140960795 + 8011712 * 2 ^ 59
def prefixEnd_8011712 : Nat := 4983230072969 + 3 ^ 40 * 8011712 * 2
def baseEnd_8011712 : Nat := 1371286373798087791218271

theorem tailTrace_8011712 : CollatzResearch.WordTrace tailWord_8011712 prefixEnd_8011712 1371286373798087791218271 := by
  unfold tailWord_8011712
  simp only [CollatzResearch.WordTrace]
  refine ⟨146105571375471595159730695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194807428500628793546307593 146105571375471595159730695)
  ·
    refine ⟨219158357063207392739596043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146105571375471595159730695 219158357063207392739596043)
    ·
      refine ⟨328737535594811089109394065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219158357063207392739596043 328737535594811089109394065)
      ·
        refine ⟨246553151696108316832045549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328737535594811089109394065 246553151696108316832045549)
        ·
          refine ⟨92457431886040618812017081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246553151696108316832045549 92457431886040618812017081)
          ·
            refine ⟨69343073914530464109012811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92457431886040618812017081 69343073914530464109012811)
            ·
              refine ⟨104014610871795696163519217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69343073914530464109012811 104014610871795696163519217)
              ·
                refine ⟨78010958153846772122639413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104014610871795696163519217 78010958153846772122639413)
                ·
                  refine ⟨7313527326923134886497445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78010958153846772122639413 7313527326923134886497445)
                  ·
                    refine ⟨1371286373798087791218271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7313527326923134886497445 1371286373798087791218271)
                    ·
                      rfl

theorem cell23_8011712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 4].length) (baseStart_8011712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011712 prefixEnd_8011712 := by exact prefixLift 8011712
  have htrace : WordTrace (prefixWord ++ tailWord_8011712) baseStart_8011712 baseEnd_8011712 := by
    simpa [prefixWord, tailWord_8011712, baseEnd_8011712] using wordTrace_append hprefix tailTrace_8011712
  have hstable : (prefixWord ++ tailWord_8011712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011712).length < 2 ^ (prefixWord ++ tailWord_8011712).sum := by decide
  have hdescent : baseEnd_8011712 < baseStart_8011712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011732 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_8011732 : Nat := 118140960795 + 8011732 * 2 ^ 59
def prefixEnd_8011732 : Nat := 4983230072969 + 3 ^ 40 * 8011732 * 2
def baseEnd_8011732 : Nat := 4113869391007353295404721

theorem tailTrace_8011732 : CollatzResearch.WordTrace tailWord_8011732 prefixEnd_8011732 4113869391007353295404721 := by
  unfold tailWord_8011732
  simp only [CollatzResearch.WordTrace]
  refine ⟨146105936105435366867594725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194807914807247155823459633 146105936105435366867594725)
  ·
    refine ⟨27394863019769131287674011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146105936105435366867594725 27394863019769131287674011)
    ·
      refine ⟨41092294529653696931511017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27394863019769131287674011 41092294529653696931511017)
      ·
        refine ⟨30819220897240272698633263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41092294529653696931511017 30819220897240272698633263)
        ·
          refine ⟨46228831345860409047949895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30819220897240272698633263 46228831345860409047949895)
          ·
            refine ⟨69343247018790613571924843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46228831345860409047949895 69343247018790613571924843)
            ·
              refine ⟨104014870528185920357887265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69343247018790613571924843 104014870528185920357887265)
              ·
                refine ⟨78011152896139440268415449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104014870528185920357887265 78011152896139440268415449)
                ·
                  refine ⟨58508364672104580201311587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78011152896139440268415449 58508364672104580201311587)
                  ·
                    refine ⟨87762547008156870301967381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58508364672104580201311587 87762547008156870301967381)
                    ·
                      refine ⟨4113869391007353295404721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87762547008156870301967381 4113869391007353295404721)
                      ·
                        rfl

theorem cell23_8011732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_8011732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011732 prefixEnd_8011732 := by exact prefixLift 8011732
  have htrace : WordTrace (prefixWord ++ tailWord_8011732) baseStart_8011732 baseEnd_8011732 := by
    simpa [prefixWord, tailWord_8011732, baseEnd_8011732] using wordTrace_append hprefix tailTrace_8011732
  have hstable : (prefixWord ++ tailWord_8011732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011732).length < 2 ^ (prefixWord ++ tailWord_8011732).sum := by decide
  have hdescent : baseEnd_8011732 < baseStart_8011732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011752 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_8011752 : Nat := 118140960795 + 8011752 * 2 ^ 59
def prefixEnd_8011752 : Nat := 4983230072969 + 3 ^ 40 * 8011752 * 2
def baseEnd_8011752 : Nat := 4113879660620443217154629

theorem tailTrace_8011752 : CollatzResearch.WordTrace tailWord_8011752 prefixEnd_8011752 4113879660620443217154629 := by
  unfold tailWord_8011752
  simp only [CollatzResearch.WordTrace]
  refine ⟨146106300835399138575458755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194808401113865518100611673 146106300835399138575458755)
  ·
    refine ⟨219159451253098707863188133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146106300835399138575458755 219159451253098707863188133)
    ·
      refine ⟨41092397109956007724347775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219159451253098707863188133 41092397109956007724347775)
      ·
        refine ⟨61638595664934011586521663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41092397109956007724347775 61638595664934011586521663)
        ·
          refine ⟨92457893497401017379782495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61638595664934011586521663 92457893497401017379782495)
          ·
            refine ⟨138686840246101526069673743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92457893497401017379782495 138686840246101526069673743)
            ·
              refine ⟨208030260369152289104510615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138686840246101526069673743 208030260369152289104510615)
              ·
                refine ⟨312045390553728433656765923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208030260369152289104510615 312045390553728433656765923)
                ·
                  refine ⟨468068085830592650485148885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312045390553728433656765923 468068085830592650485148885)
                  ·
                    refine ⟨10970345761654515245745677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 468068085830592650485148885 10970345761654515245745677)
                    ·
                      refine ⟨4113879660620443217154629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10970345761654515245745677 4113879660620443217154629)
                      ·
                        rfl

theorem cell23_8011752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_8011752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011752 prefixEnd_8011752 := by exact prefixLift 8011752
  have htrace : WordTrace (prefixWord ++ tailWord_8011752) baseStart_8011752 baseEnd_8011752 := by
    simpa [prefixWord, tailWord_8011752, baseEnd_8011752] using wordTrace_append hprefix tailTrace_8011752
  have hstable : (prefixWord ++ tailWord_8011752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011752).length < 2 ^ (prefixWord ++ tailWord_8011752).sum := by decide
  have hdescent : baseEnd_8011752 < baseStart_8011752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011755 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 2, 9]
def baseStart_8011755 : Nat := 118140960795 + 8011755 * 2 ^ 59
def prefixEnd_8011755 : Nat := 4983230072969 + 3 ^ 40 * 8011755 * 2
def baseEnd_8011755 : Nat := 1371293733687468901805705

theorem tailTrace_8011755 : CollatzResearch.WordTrace tailWord_8011755 prefixEnd_8011755 1371293733687468901805705 := by
  unfold tailWord_8011755
  simp only [CollatzResearch.WordTrace]
  refine ⟨292212711089787408663276719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194808474059858272442184479 292212711089787408663276719)
  ·
    refine ⟨438319066634681112994915079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292212711089787408663276719 438319066634681112994915079)
    ·
      refine ⟨657478599952021669492372619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438319066634681112994915079 657478599952021669492372619)
      ·
        refine ⟨986217899928032504238558929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657478599952021669492372619 986217899928032504238558929)
        ·
          refine ⟨739663424946024378178919197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 986217899928032504238558929 739663424946024378178919197)
          ·
            refine ⟨277373784354759141817094699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 739663424946024378178919197 277373784354759141817094699)
            ·
              refine ⟨416060676532138712725642049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277373784354759141817094699 416060676532138712725642049)
              ·
                refine ⟨312045507399104034544231537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416060676532138712725642049 312045507399104034544231537)
                ·
                  refine ⟨234034130549328025908173653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312045507399104034544231537 234034130549328025908173653)
                  ·
                    refine ⟨1371293733687468901805705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 234034130549328025908173653 1371293733687468901805705)
                    ·
                      rfl

theorem cell23_8011755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 9].length) (baseStart_8011755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011755 prefixEnd_8011755 := by exact prefixLift 8011755
  have htrace : WordTrace (prefixWord ++ tailWord_8011755) baseStart_8011755 baseEnd_8011755 := by
    simpa [prefixWord, tailWord_8011755, baseEnd_8011755] using wordTrace_append hprefix tailTrace_8011755
  have hstable : (prefixWord ++ tailWord_8011755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011755).length < 2 ^ (prefixWord ++ tailWord_8011755).sum := by decide
  have hdescent : baseEnd_8011755 < baseStart_8011755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011780 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_8011780 : Nat := 118140960795 + 8011780 * 2 ^ 59
def prefixEnd_8011780 : Nat := 4983230072969 + 3 ^ 40 * 8011780 * 2
def baseEnd_8011780 : Nat := 1371298012692923035868167

theorem tailTrace_8011780 : CollatzResearch.WordTrace tailWord_8011780 prefixEnd_8011780 1371298012692923035868167 := by
  unfold tailWord_8011780
  simp only [CollatzResearch.WordTrace]
  refine ⟨146106811457348418966468397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194809081943131225288624529 146106811457348418966468397)
  ·
    refine ⟨54790054296505657112425649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146106811457348418966468397 54790054296505657112425649)
    ·
      refine ⟨41092540722379242834319237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54790054296505657112425649 41092540722379242834319237)
      ·
        refine ⟨7704851385446108031434857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41092540722379242834319237 7704851385446108031434857)
        ·
          refine ⟨5778638539084581023576143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7704851385446108031434857 5778638539084581023576143)
          ·
            refine ⟨8667957808626871535364215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5778638539084581023576143 8667957808626871535364215)
            ·
              refine ⟨13001936712940307303046323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8667957808626871535364215 13001936712940307303046323)
              ·
                refine ⟨19502905069410460954569485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13001936712940307303046323 19502905069410460954569485)
                ·
                  refine ⟨7313589401028922857963557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19502905069410460954569485 7313589401028922857963557)
                  ·
                    refine ⟨1371298012692923035868167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7313589401028922857963557 1371298012692923035868167)
                    ·
                      rfl

theorem cell23_8011780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_8011780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011780 prefixEnd_8011780 := by exact prefixLift 8011780
  have htrace : WordTrace (prefixWord ++ tailWord_8011780) baseStart_8011780 baseEnd_8011780 := by
    simpa [prefixWord, tailWord_8011780, baseEnd_8011780] using wordTrace_append hprefix tailTrace_8011780
  have hstable : (prefixWord ++ tailWord_8011780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011780).length < 2 ^ (prefixWord ++ tailWord_8011780).sum := by decide
  have hdescent : baseEnd_8011780 < baseStart_8011780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011792 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_8011792 : Nat := 118140960795 + 8011792 * 2 ^ 59
def prefixEnd_8011792 : Nat := 4983230072969 + 3 ^ 40 * 8011792 * 2
def baseEnd_8011792 : Nat := 4113900199846623060654445

theorem tailTrace_8011792 : CollatzResearch.WordTrace tailWord_8011792 prefixEnd_8011792 4113900199846623060654445 := by
  unfold tailWord_8011792
  simp only [CollatzResearch.WordTrace]
  refine ⟨146107030295326681991186815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194809373727102242654915753 146107030295326681991186815)
  ·
    refine ⟨219160545442990022986780223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146107030295326681991186815 219160545442990022986780223)
    ·
      refine ⟨328740818164485034480170335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219160545442990022986780223 328740818164485034480170335)
      ·
        refine ⟨493111227246727551720255503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328740818164485034480170335 493111227246727551720255503)
        ·
          refine ⟨739666840870091327580383255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493111227246727551720255503 739666840870091327580383255)
          ·
            refine ⟨1109500261305136991370574883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739666840870091327580383255 1109500261305136991370574883)
            ·
              refine ⟨1664250391957705487055862325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1109500261305136991370574883 1664250391957705487055862325)
              ·
                refine ⟨156023474246034889411487093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1664250391957705487055862325 156023474246034889411487093)
                ·
                  refine ⟨14627200710565770882326915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156023474246034889411487093 14627200710565770882326915)
                  ·
                    refine ⟨21940801065848656323490373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14627200710565770882326915 21940801065848656323490373)
                    ·
                      refine ⟨4113900199846623060654445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21940801065848656323490373 4113900199846623060654445)
                      ·
                        rfl

theorem cell23_8011792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_8011792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011792 prefixEnd_8011792 := by exact prefixLift 8011792
  have htrace : WordTrace (prefixWord ++ tailWord_8011792) baseStart_8011792 baseEnd_8011792 := by
    simpa [prefixWord, tailWord_8011792, baseEnd_8011792] using wordTrace_append hprefix tailTrace_8011792
  have hstable : (prefixWord ++ tailWord_8011792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011792).length < 2 ^ (prefixWord ++ tailWord_8011792).sum := by decide
  have hdescent : baseEnd_8011792 < baseStart_8011792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011829 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_8011829 : Nat := 118140960795 + 8011829 * 2 ^ 59
def prefixEnd_8011829 : Nat := 4983230072969 + 3 ^ 40 * 8011829 * 2
def baseEnd_8011829 : Nat := 4113919198630839415891775

theorem tailTrace_8011829 : CollatzResearch.WordTrace tailWord_8011829 prefixEnd_8011829 4113919198630839415891775 := by
  unfold tailWord_8011829
  simp only [CollatzResearch.WordTrace]
  refine ⟨292215410091519319301470541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194810273394346212867647027 292215410091519319301470541)
  ·
    refine ⟨109580778784319744738051453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292215410091519319301470541 109580778784319744738051453)
    ·
      refine ⟨41092792044119904276769295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109580778784319744738051453 41092792044119904276769295)
      ·
        refine ⟨61639188066179856415153943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41092792044119904276769295 61639188066179856415153943)
        ·
          refine ⟨92458782099269784622730915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61639188066179856415153943 92458782099269784622730915)
          ·
            refine ⟨138688173148904676934096373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92458782099269784622730915 138688173148904676934096373)
            ·
              refine ⟨13002016232709813462571535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138688173148904676934096373 13002016232709813462571535)
              ·
                refine ⟨19503024349064720193857303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13002016232709813462571535 19503024349064720193857303)
                ·
                  refine ⟨29254536523597080290785955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19503024349064720193857303 29254536523597080290785955)
                  ·
                    refine ⟨43881804785395620436178933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29254536523597080290785955 43881804785395620436178933)
                    ·
                      refine ⟨4113919198630839415891775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43881804785395620436178933 4113919198630839415891775)
                      ·
                        rfl

theorem cell23_8011829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_8011829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011829 prefixEnd_8011829 := by exact prefixLift 8011829
  have htrace : WordTrace (prefixWord ++ tailWord_8011829) baseStart_8011829 baseEnd_8011829 := by
    simpa [prefixWord, tailWord_8011829, baseEnd_8011829] using wordTrace_append hprefix tailTrace_8011829
  have hstable : (prefixWord ++ tailWord_8011829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011829).length < 2 ^ (prefixWord ++ tailWord_8011829).sum := by decide
  have hdescent : baseEnd_8011829 < baseStart_8011829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011832 : List Nat := [2, 1, 2, 1, 6, 11]
def baseStart_8011832 : Nat := 118140960795 + 8011832 * 2 ^ 59
def prefixEnd_8011832 : Nat := 4983230072969 + 3 ^ 40 * 8011832 * 2
def baseEnd_8011832 : Nat := 16929714975608242403927

theorem tailTrace_8011832 : CollatzResearch.WordTrace tailWord_8011832 prefixEnd_8011832 16929714975608242403927 := by
  unfold tailWord_8011832
  simp only [CollatzResearch.WordTrace]
  refine ⟨146107759755254225406914875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194810346340338967209219833 146107759755254225406914875)
  ·
    refine ⟨219161639632881338110372313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146107759755254225406914875 219161639632881338110372313)
    ·
      refine ⟨164371229724661003582779235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219161639632881338110372313 164371229724661003582779235)
      ·
        refine ⟨246556844586991505374168853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164371229724661003582779235 246556844586991505374168853)
        ·
          refine ⟨11557352090015226814414165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246556844586991505374168853 11557352090015226814414165)
          ·
            refine ⟨16929714975608242403927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11557352090015226814414165 16929714975608242403927)
            ·
              rfl

theorem cell23_8011832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 11].length) (baseStart_8011832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011832 prefixEnd_8011832 := by exact prefixLift 8011832
  have htrace : WordTrace (prefixWord ++ tailWord_8011832) baseStart_8011832 baseEnd_8011832 := by
    simpa [prefixWord, tailWord_8011832, baseEnd_8011832] using wordTrace_append hprefix tailTrace_8011832
  have hstable : (prefixWord ++ tailWord_8011832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011832).length < 2 ^ (prefixWord ++ tailWord_8011832).sum := by decide
  have hdescent : baseEnd_8011832 < baseStart_8011832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011836 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_8011836 : Nat := 118140960795 + 8011836 * 2 ^ 59
def prefixEnd_8011836 : Nat := 4983230072969 + 3 ^ 40 * 8011836 * 2
def baseEnd_8011836 : Nat := 1371307597665140296168081

theorem tailTrace_8011836 : CollatzResearch.WordTrace tailWord_8011836 prefixEnd_8011836 1371307597665140296168081 := by
  unfold tailWord_8011836
  simp only [CollatzResearch.WordTrace]
  refine ⟨146107832701246979748487681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194810443601662639664650241 146107832701246979748487681)
  ·
    refine ⟨109580874525935234811365761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146107832701246979748487681 109580874525935234811365761)
    ·
      refine ⟨82185655894451426108524321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109580874525935234811365761 82185655894451426108524321)
      ·
        refine ⟨61639241920838569581393241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82185655894451426108524321 61639241920838569581393241)
        ·
          refine ⟨46229431440628927186044931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61639241920838569581393241 46229431440628927186044931)
          ·
            refine ⟨69344147160943390779067397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46229431440628927186044931 69344147160943390779067397)
            ·
              refine ⟨13002027592676885771075137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69344147160943390779067397 13002027592676885771075137)
              ·
                refine ⟨9751520694507664328306353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13002027592676885771075137 9751520694507664328306353)
                ·
                  refine ⟨7313640520880748246229765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9751520694507664328306353 7313640520880748246229765)
                  ·
                    refine ⟨1371307597665140296168081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7313640520880748246229765 1371307597665140296168081)
                    ·
                      rfl

theorem cell23_8011836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_8011836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011836 prefixEnd_8011836 := by exact prefixLift 8011836
  have htrace : WordTrace (prefixWord ++ tailWord_8011836) baseStart_8011836 baseEnd_8011836 := by
    simpa [prefixWord, tailWord_8011836, baseEnd_8011836] using wordTrace_append hprefix tailTrace_8011836
  have hstable : (prefixWord ++ tailWord_8011836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011836).length < 2 ^ (prefixWord ++ tailWord_8011836).sum := by decide
  have hdescent : baseEnd_8011836 < baseStart_8011836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011846 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_8011846 : Nat := 118140960795 + 8011846 * 2 ^ 59
def prefixEnd_8011846 : Nat := 4983230072969 + 3 ^ 40 * 8011846 * 2
def baseEnd_8011846 : Nat := 4113927927801965849379197

theorem tailTrace_8011846 : CollatzResearch.WordTrace tailWord_8011846 prefixEnd_8011846 4113927927801965849379197 := by
  unfold tailWord_8011846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9131750941639304100151231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194810686754971820803226261 9131750941639304100151231)
  ·
    refine ⟨13697626412458956150226847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9131750941639304100151231 13697626412458956150226847)
    ·
      refine ⟨20546439618688434225340271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13697626412458956150226847 20546439618688434225340271)
      ·
        refine ⟨30819659428032651338010407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20546439618688434225340271 30819659428032651338010407)
        ·
          refine ⟨46229489142048977007015611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30819659428032651338010407 46229489142048977007015611)
          ·
            refine ⟨69344233713073465510523417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46229489142048977007015611 69344233713073465510523417)
            ·
              refine ⟨52008175284805099132892563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69344233713073465510523417 52008175284805099132892563)
              ·
                refine ⟨78012262927207648699338845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52008175284805099132892563 78012262927207648699338845)
                ·
                  refine ⟨29254598597702868262252067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78012262927207648699338845 29254598597702868262252067)
                  ·
                    refine ⟨43881897896554302393378101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29254598597702868262252067 43881897896554302393378101)
                    ·
                      refine ⟨4113927927801965849379197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43881897896554302393378101 4113927927801965849379197)
                      ·
                        rfl

theorem cell23_8011846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_8011846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011846 prefixEnd_8011846 := by exact prefixLift 8011846
  have htrace : WordTrace (prefixWord ++ tailWord_8011846) baseStart_8011846 baseEnd_8011846 := by
    simpa [prefixWord, tailWord_8011846, baseEnd_8011846] using wordTrace_append hprefix tailTrace_8011846
  have hstable : (prefixWord ++ tailWord_8011846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011846).length < 2 ^ (prefixWord ++ tailWord_8011846).sum := by decide
  have hdescent : baseEnd_8011846 < baseStart_8011846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011852 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_8011852 : Nat := 118140960795 + 8011852 * 2 ^ 59
def prefixEnd_8011852 : Nat := 4983230072969 + 3 ^ 40 * 8011852 * 2
def baseEnd_8011852 : Nat := 4113931008685892825904169

theorem tailTrace_8011852 : CollatzResearch.WordTrace tailWord_8011852 prefixEnd_8011852 4113931008685892825904169 := by
  unfold tailWord_8011852
  simp only [CollatzResearch.WordTrace]
  refine ⟨146108124485217997114778905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194810832646957329486371873 146108124485217997114778905)
  ·
    refine ⟨109581093363913497836084179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146108124485217997114778905 109581093363913497836084179)
    ·
      refine ⟨164371640045870246754126269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109581093363913497836084179 164371640045870246754126269)
      ·
        refine ⟨61639365017201342532797351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164371640045870246754126269 61639365017201342532797351)
        ·
          refine ⟨92459047525802013799196027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61639365017201342532797351 92459047525802013799196027)
          ·
            refine ⟨138688571288703020698794041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92459047525802013799196027 138688571288703020698794041)
            ·
              refine ⟨104016428466527265524095531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138688571288703020698794041 104016428466527265524095531)
              ·
                refine ⟨156024642699790898286143297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104016428466527265524095531 156024642699790898286143297)
                ·
                  refine ⟨117018482024843173714607473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156024642699790898286143297 117018482024843173714607473)
                  ·
                    refine ⟨87763861518632380285955605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117018482024843173714607473 87763861518632380285955605)
                    ·
                      refine ⟨4113931008685892825904169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87763861518632380285955605 4113931008685892825904169)
                      ·
                        rfl

theorem cell23_8011852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_8011852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011852 prefixEnd_8011852 := by exact prefixLift 8011852
  have htrace : WordTrace (prefixWord ++ tailWord_8011852) baseStart_8011852 baseEnd_8011852 := by
    simpa [prefixWord, tailWord_8011852, baseEnd_8011852] using wordTrace_append hprefix tailTrace_8011852
  have hstable : (prefixWord ++ tailWord_8011852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011852).length < 2 ^ (prefixWord ++ tailWord_8011852).sum := by decide
  have hdescent : baseEnd_8011852 < baseStart_8011852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011899 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 8, 2]
def baseStart_8011899 : Nat := 118140960795 + 8011899 * 2 ^ 59
def prefixEnd_8011899 : Nat := 4983230072969 + 3 ^ 40 * 8011899 * 2
def baseEnd_8011899 : Nat := 4113955142276654142016453

theorem tailTrace_8011899 : CollatzResearch.WordTrace tailWord_8011899 prefixEnd_8011899 4113955142276654142016453 := by
  unfold tailWord_8011899
  simp only [CollatzResearch.WordTrace]
  refine ⟨292217963201265721256518751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194811975467510480837679167 292217963201265721256518751)
  ·
    refine ⟨438326944801898581884778127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292217963201265721256518751 438326944801898581884778127)
    ·
      refine ⟨657490417202847872827167191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438326944801898581884778127 657490417202847872827167191)
      ·
        refine ⟨986235625804271809240750787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657490417202847872827167191 986235625804271809240750787)
        ·
          refine ⟨1479353438706407713861126181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986235625804271809240750787 1479353438706407713861126181)
          ·
            refine ⟨277378769757451446348961159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1479353438706407713861126181 277378769757451446348961159)
            ·
              refine ⟨416068154636177169523441739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277378769757451446348961159 416068154636177169523441739)
              ·
                refine ⟨624102231954265754285162609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416068154636177169523441739 624102231954265754285162609)
                ·
                  refine ⟨468076673965699315713871957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624102231954265754285162609 468076673965699315713871957)
                  ·
                    refine ⟨5485273523035538856021937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 468076673965699315713871957 5485273523035538856021937)
                    ·
                      refine ⟨4113955142276654142016453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485273523035538856021937 4113955142276654142016453)
                      ·
                        rfl

theorem cell23_8011899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 8, 2].length) (baseStart_8011899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011899 prefixEnd_8011899 := by exact prefixLift 8011899
  have htrace : WordTrace (prefixWord ++ tailWord_8011899) baseStart_8011899 baseEnd_8011899 := by
    simpa [prefixWord, tailWord_8011899, baseEnd_8011899] using wordTrace_append hprefix tailTrace_8011899
  have hstable : (prefixWord ++ tailWord_8011899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011899).length < 2 ^ (prefixWord ++ tailWord_8011899).sum := by decide
  have hdescent : baseEnd_8011899 < baseStart_8011899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011909 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_8011909 : Nat := 118140960795 + 8011909 * 2 ^ 59
def prefixEnd_8011909 : Nat := 4983230072969 + 3 ^ 40 * 8011909 * 2
def baseEnd_8011909 : Nat := 1371320092361066367630469

theorem tailTrace_8011909 : CollatzResearch.WordTrace tailWord_8011909 prefixEnd_8011909 1371320092361066367630469 := by
  unfold tailWord_8011909
  simp only [CollatzResearch.WordTrace]
  refine ⟨292218327931229492964382781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194812218620819661976255187 292218327931229492964382781)
  ·
    refine ⟨109581872974211059861643543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292218327931229492964382781 109581872974211059861643543)
    ·
      refine ⟨164372809461316589792465315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109581872974211059861643543 164372809461316589792465315)
      ·
        refine ⟨246559214191974884688697973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164372809461316589792465315 246559214191974884688697973)
        ·
          refine ⟨23114926330497645439565435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 246559214191974884688697973 23114926330497645439565435)
          ·
            refine ⟨34672389495746468159348153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23114926330497645439565435 34672389495746468159348153)
            ·
              refine ⟨26004292121809851119511115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34672389495746468159348153 26004292121809851119511115)
              ·
                refine ⟨39006438182714776679266673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26004292121809851119511115 39006438182714776679266673)
                ·
                  refine ⟨29254828637036082509450005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39006438182714776679266673 29254828637036082509450005)
                  ·
                    refine ⟨1371320092361066367630469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29254828637036082509450005 1371320092361066367630469)
                    ·
                      rfl

theorem cell23_8011909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_8011909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011909 prefixEnd_8011909 := by exact prefixLift 8011909
  have htrace : WordTrace (prefixWord ++ tailWord_8011909) baseStart_8011909 baseEnd_8011909 := by
    simpa [prefixWord, tailWord_8011909, baseEnd_8011909] using wordTrace_append hprefix tailTrace_8011909
  have hstable : (prefixWord ++ tailWord_8011909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011909).length < 2 ^ (prefixWord ++ tailWord_8011909).sum := by decide
  have hdescent : baseEnd_8011909 < baseStart_8011909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011933 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_8011933 : Nat := 118140960795 + 8011933 * 2 ^ 59
def prefixEnd_8011933 : Nat := 4983230072969 + 3 ^ 40 * 8011933 * 2
def baseEnd_8011933 : Nat := 4113972600618907008991297

theorem tailTrace_8011933 : CollatzResearch.WordTrace tailWord_8011933 prefixEnd_8011933 4113972600618907008991297 := by
  unfold tailWord_8011933
  simp only [CollatzResearch.WordTrace]
  refine ⟨292219203283142545063256453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194812802188761696708837635 292219203283142545063256453)
  ·
    refine ⟨54791100615589227199360585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 292219203283142545063256453 54791100615589227199360585)
    ·
      refine ⟨41093325461691920399520439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54791100615589227199360585 41093325461691920399520439)
      ·
        refine ⟨61639988192537880599280659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41093325461691920399520439 61639988192537880599280659)
        ·
          refine ⟨92459982288806820898920989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61639988192537880599280659 92459982288806820898920989)
          ·
            refine ⟨34672493358302557837095371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92459982288806820898920989 34672493358302557837095371)
            ·
              refine ⟨52008740037453836755643057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34672493358302557837095371 52008740037453836755643057)
              ·
                refine ⟨39006555028090377566732293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52008740037453836755643057 39006555028090377566732293)
                ·
                  refine ⟨7313729067766945793762305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39006555028090377566732293 7313729067766945793762305)
                  ·
                    refine ⟨5485296800825209345321729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7313729067766945793762305 5485296800825209345321729)
                    ·
                      refine ⟨4113972600618907008991297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5485296800825209345321729 4113972600618907008991297)
                      ·
                        rfl

theorem cell23_8011933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_8011933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011933 prefixEnd_8011933 := by exact prefixLift 8011933
  have htrace : WordTrace (prefixWord ++ tailWord_8011933) baseStart_8011933 baseEnd_8011933 := by
    simpa [prefixWord, tailWord_8011933, baseEnd_8011933] using wordTrace_append hprefix tailTrace_8011933
  have hstable : (prefixWord ++ tailWord_8011933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011933).length < 2 ^ (prefixWord ++ tailWord_8011933).sum := by decide
  have hdescent : baseEnd_8011933 < baseStart_8011933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8011986 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_8011986 : Nat := 118140960795 + 8011986 * 2 ^ 59
def prefixEnd_8011986 : Nat := 4983230072969 + 3 ^ 40 * 8011986 * 2
def baseEnd_8011986 : Nat := 1371333271697865100542851

theorem tailTrace_8011986 : CollatzResearch.WordTrace tailWord_8011986 prefixEnd_8011986 1371333271697865100542851 := by
  unfold tailWord_8011986
  simp only [CollatzResearch.WordTrace]
  refine ⟨73055284087987633778733953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194814090901300356743290541 73055284087987633778733953)
  ·
    refine ⟨54791463065990725334050465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73055284087987633778733953 54791463065990725334050465)
    ·
      refine ⟨41093597299493044000537849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54791463065990725334050465 41093597299493044000537849)
      ·
        refine ⟨30820197974619783000403387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41093597299493044000537849 30820197974619783000403387)
        ·
          refine ⟨46230296961929674500605081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30820197974619783000403387 46230296961929674500605081)
          ·
            refine ⟨34672722721447255875453811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46230296961929674500605081 34672722721447255875453811)
            ·
              refine ⟨52009084082170883813180717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34672722721447255875453811 52009084082170883813180717)
              ·
                refine ⟨19503406530814081429942769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52009084082170883813180717 19503406530814081429942769)
                ·
                  refine ⟨14627554898110561072457077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19503406530814081429942769 14627554898110561072457077)
                  ·
                    refine ⟨1371333271697865100542851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14627554898110561072457077 1371333271697865100542851)
                    ·
                      rfl

theorem cell23_8011986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_8011986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8011986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8011986 prefixEnd_8011986 := by exact prefixLift 8011986
  have htrace : WordTrace (prefixWord ++ tailWord_8011986) baseStart_8011986 baseEnd_8011986 := by
    simpa [prefixWord, tailWord_8011986, baseEnd_8011986] using wordTrace_append hprefix tailTrace_8011986
  have hstable : (prefixWord ++ tailWord_8011986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8011986).length < 2 ^ (prefixWord ++ tailWord_8011986).sum := by decide
  have hdescent : baseEnd_8011986 < baseStart_8011986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8011986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012063 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 6]
def baseStart_8012063 : Nat := 118140960795 + 8012063 * 2 ^ 59
def prefixEnd_8012063 : Nat := 4983230072969 + 3 ^ 40 * 8012063 * 2
def baseEnd_8012063 : Nat := 457115483678221277818411

theorem tailTrace_8012063 : CollatzResearch.WordTrace tailWord_8012063 prefixEnd_8012063 457115483678221277818411 := by
  unfold tailWord_8012063
  simp only [CollatzResearch.WordTrace]
  refine ⟨292223944772671577265488843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194815963181781051510325895 292223944772671577265488843)
  ·
    refine ⟨438335917159007365898233265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292223944772671577265488843 438335917159007365898233265)
    ·
      refine ⟨328751937869255524423674949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438335917159007365898233265 328751937869255524423674949)
      ·
        refine ⟨61640988350485410829439053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 328751937869255524423674949 61640988350485410829439053)
        ·
          refine ⟨23115370631432029061039645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61640988350485410829439053 23115370631432029061039645)
          ·
            refine ⟨8668263986787010897889867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23115370631432029061039645 8668263986787010897889867)
            ·
              refine ⟨13002395980180516346834801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668263986787010897889867 13002395980180516346834801)
              ·
                refine ⟨9751796985135387260126101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13002395980180516346834801 9751796985135387260126101)
                ·
                  refine ⟨457115483678221277818411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9751796985135387260126101 457115483678221277818411)
                  ·
                    rfl

theorem cell23_8012063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 6].length) (baseStart_8012063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012063 prefixEnd_8012063 := by exact prefixLift 8012063
  have htrace : WordTrace (prefixWord ++ tailWord_8012063) baseStart_8012063 baseEnd_8012063 := by
    simpa [prefixWord, tailWord_8012063, baseEnd_8012063] using wordTrace_append hprefix tailTrace_8012063
  have hstable : (prefixWord ++ tailWord_8012063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012063).length < 2 ^ (prefixWord ++ tailWord_8012063).sum := by decide
  have hdescent : baseEnd_8012063 < baseStart_8012063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012066 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_8012066 : Nat := 118140960795 + 8012066 * 2 ^ 59
def prefixEnd_8012066 : Nat := 4983230072969 + 3 ^ 40 * 8012066 * 2
def baseEnd_8012066 : Nat := 4114040893545954988628185

theorem tailTrace_8012066 : CollatzResearch.WordTrace tailWord_8012066 prefixEnd_8012066 4114040893545954988628185 := by
  unfold tailWord_8012066
  simp only [CollatzResearch.WordTrace]
  refine ⟨73056013547915177194462013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194816036127773805851898701 73056013547915177194462013)
  ·
    refine ⟨27396005080468191447923255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73056013547915177194462013 27396005080468191447923255)
    ·
      refine ⟨41094007620702287171884883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27396005080468191447923255 41094007620702287171884883)
      ·
        refine ⟨61641011431053430757827325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41094007620702287171884883 61641011431053430757827325)
        ·
          refine ⟨23115379286645036534185247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61641011431053430757827325 23115379286645036534185247)
          ·
            refine ⟨34673068929967554801277871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23115379286645036534185247 34673068929967554801277871)
            ·
              refine ⟨52009603394951332201916807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34673068929967554801277871 52009603394951332201916807)
              ·
                refine ⟨78014405092426998302875211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52009603394951332201916807 78014405092426998302875211)
                ·
                  refine ⟨117021607638640497454312817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78014405092426998302875211 117021607638640497454312817)
                  ·
                    refine ⟨87766205728980373090734613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117021607638640497454312817 87766205728980373090734613)
                    ·
                      refine ⟨4114040893545954988628185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87766205728980373090734613 4114040893545954988628185)
                      ·
                        rfl

theorem cell23_8012066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_8012066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012066 prefixEnd_8012066 := by exact prefixLift 8012066
  have htrace : WordTrace (prefixWord ++ tailWord_8012066) baseStart_8012066 baseEnd_8012066 := by
    simpa [prefixWord, tailWord_8012066, baseEnd_8012066] using wordTrace_append hprefix tailTrace_8012066
  have hstable : (prefixWord ++ tailWord_8012066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012066).length < 2 ^ (prefixWord ++ tailWord_8012066).sum := by decide
  have hdescent : baseEnd_8012066 < baseStart_8012066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012113 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_8012113 : Nat := 118140960795 + 8012113 * 2 ^ 59
def prefixEnd_8012113 : Nat := 4983230072969 + 3 ^ 40 * 8012113 * 2
def baseEnd_8012113 : Nat := 4114065027136716304740469

theorem tailTrace_8012113 : CollatzResearch.WordTrace tailWord_8012113 prefixEnd_8012113 4114065027136716304740469 := by
  unfold tailWord_8012113
  simp only [CollatzResearch.WordTrace]
  refine ⟨292225768422490435804808993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194817178948326957203205995 292225768422490435804808993)
  ·
    refine ⟨219169326316867826853606745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292225768422490435804808993 219169326316867826853606745)
    ·
      refine ⟨164376994737650870140205059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219169326316867826853606745 164376994737650870140205059)
      ·
        refine ⟨246565492106476305210307589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164376994737650870140205059 246565492106476305210307589)
        ·
          refine ⟨46231029769964307226932673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 246565492106476305210307589 46231029769964307226932673)
          ·
            refine ⟨34673272327473230420199505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46231029769964307226932673 34673272327473230420199505)
            ·
              refine ⟨26004954245604922815149629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34673272327473230420199505 26004954245604922815149629)
              ·
                refine ⟨9751857842101846055681111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26004954245604922815149629 9751857842101846055681111)
                ·
                  refine ⟨14627786763152769083521667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9751857842101846055681111 14627786763152769083521667)
                  ·
                    refine ⟨21941680144729153625282501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14627786763152769083521667 21941680144729153625282501)
                    ·
                      refine ⟨4114065027136716304740469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21941680144729153625282501 4114065027136716304740469)
                      ·
                        rfl

theorem cell23_8012113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_8012113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012113 prefixEnd_8012113 := by exact prefixLift 8012113
  have htrace : WordTrace (prefixWord ++ tailWord_8012113) baseStart_8012113 baseEnd_8012113 := by
    simpa [prefixWord, tailWord_8012113, baseEnd_8012113] using wordTrace_append hprefix tailTrace_8012113
  have hstable : (prefixWord ++ tailWord_8012113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012113).length < 2 ^ (prefixWord ++ tailWord_8012113).sum := by decide
  have hdescent : baseEnd_8012113 < baseStart_8012113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012124 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_8012124 : Nat := 118140960795 + 8012124 * 2 ^ 59
def prefixEnd_8012124 : Nat := 4983230072969 + 3 ^ 40 * 8012124 * 2
def baseEnd_8012124 : Nat := 4114070675423915761702919

theorem tailTrace_8012124 : CollatzResearch.WordTrace tailWord_8012124 prefixEnd_8012124 4114070675423915761702919 := by
  unfold tailWord_8012124
  simp only [CollatzResearch.WordTrace]
  refine ⟨146113084812725292341729713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194817446416967056455639617 146113084812725292341729713)
  ·
    refine ⟨109584813609543969256297285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146113084812725292341729713 109584813609543969256297285)
    ·
      refine ⟨20547152551789494235555741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109584813609543969256297285 20547152551789494235555741)
      ·
        refine ⟨7705182206921060338333403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20547152551789494235555741 7705182206921060338333403)
        ·
          refine ⟨11557773310381590507500105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7705182206921060338333403 11557773310381590507500105)
          ·
            refine ⟨8668329982786192880625079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11557773310381590507500105 8668329982786192880625079)
            ·
              refine ⟨13002494974179289320937619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668329982786192880625079 13002494974179289320937619)
              ·
                refine ⟨19503742461268933981406429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13002494974179289320937619 19503742461268933981406429)
                ·
                  refine ⟨7313903422975850243027411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19503742461268933981406429 7313903422975850243027411)
                  ·
                    refine ⟨10970855134463775364541117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7313903422975850243027411 10970855134463775364541117)
                    ·
                      refine ⟨4114070675423915761702919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10970855134463775364541117 4114070675423915761702919)
                      ·
                        rfl

theorem cell23_8012124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_8012124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012124 prefixEnd_8012124 := by exact prefixLift 8012124
  have htrace : WordTrace (prefixWord ++ tailWord_8012124) baseStart_8012124 baseEnd_8012124 := by
    simpa [prefixWord, tailWord_8012124, baseEnd_8012124] using wordTrace_append hprefix tailTrace_8012124
  have hstable : (prefixWord ++ tailWord_8012124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012124).length < 2 ^ (prefixWord ++ tailWord_8012124).sum := by decide
  have hdescent : baseEnd_8012124 < baseStart_8012124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012136 : List Nat := [2, 1, 4, 2, 2, 1, 1, 10]
def baseStart_8012136 : Nat := 118140960795 + 8012136 * 2 ^ 59
def prefixEnd_8012136 : Nat := 4983230072969 + 3 ^ 40 * 8012136 * 2
def baseEnd_8012136 : Nat := 152373216192287767213069

theorem tailTrace_8012136 : CollatzResearch.WordTrace tailWord_8012136 prefixEnd_8012136 152373216192287767213069 := by
  unfold tailWord_8012136
  simp only [CollatzResearch.WordTrace]
  refine ⟨146113303650703555366448131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194817738200938073821930841 146113303650703555366448131)
  ·
    refine ⟨219169955476055333049672197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146113303650703555366448131 219169955476055333049672197)
    ·
      refine ⟨41094366651760374946813537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219169955476055333049672197 41094366651760374946813537)
      ·
        refine ⟨30820774988820281210110153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41094366651760374946813537 30820774988820281210110153)
        ·
          refine ⟨23115581241615210907582615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30820774988820281210110153 23115581241615210907582615)
          ·
            refine ⟨34673371862422816361373923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23115581241615210907582615 34673371862422816361373923)
            ·
              refine ⟨52010057793634224542060885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34673371862422816361373923 52010057793634224542060885)
              ·
                refine ⟨152373216192287767213069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52010057793634224542060885 152373216192287767213069)
                ·
                  rfl

theorem cell23_8012136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 10].length) (baseStart_8012136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012136 prefixEnd_8012136 := by exact prefixLift 8012136
  have htrace : WordTrace (prefixWord ++ tailWord_8012136) baseStart_8012136 baseEnd_8012136 := by
    simpa [prefixWord, tailWord_8012136, baseEnd_8012136] using wordTrace_append hprefix tailTrace_8012136
  have hstable : (prefixWord ++ tailWord_8012136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012136).length < 2 ^ (prefixWord ++ tailWord_8012136).sum := by decide
  have hdescent : baseEnd_8012136 < baseStart_8012136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012140 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_8012140 : Nat := 118140960795 + 8012140 * 2 ^ 59
def prefixEnd_8012140 : Nat := 4983230072969 + 3 ^ 40 * 8012140 * 2
def baseEnd_8012140 : Nat := 1371359630371462566367615

theorem tailTrace_8012140 : CollatzResearch.WordTrace tailWord_8012140 prefixEnd_8012140 1371359630371462566367615 := by
  unfold tailWord_8012140
  simp only [CollatzResearch.WordTrace]
  refine ⟨146113376596696309708020937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194817835462261746277361249 146113376596696309708020937)
  ·
    refine ⟨109585032447522232281015703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146113376596696309708020937 109585032447522232281015703)
    ·
      refine ⟨164377548671283348421523555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109585032447522232281015703 164377548671283348421523555)
      ·
        refine ⟨246566323006925022632285333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164377548671283348421523555 246566323006925022632285333)
        ·
          refine ⟨11557796390949610435888375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 246566323006925022632285333 11557796390949610435888375)
          ·
            refine ⟨17336694586424415653832563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11557796390949610435888375 17336694586424415653832563)
            ·
              refine ⟨26005041879636623480748845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17336694586424415653832563 26005041879636623480748845)
              ·
                refine ⟨9751890704863733805280817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26005041879636623480748845 9751890704863733805280817)
                ·
                  refine ⟨7313918028647800353960613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9751890704863733805280817 7313918028647800353960613)
                  ·
                    refine ⟨1371359630371462566367615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7313918028647800353960613 1371359630371462566367615)
                    ·
                      rfl

theorem cell23_8012140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_8012140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012140 prefixEnd_8012140 := by exact prefixLift 8012140
  have htrace : WordTrace (prefixWord ++ tailWord_8012140) baseStart_8012140 baseEnd_8012140 := by
    simpa [prefixWord, tailWord_8012140, baseEnd_8012140] using wordTrace_append hprefix tailTrace_8012140
  have hstable : (prefixWord ++ tailWord_8012140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012140).length < 2 ^ (prefixWord ++ tailWord_8012140).sum := by decide
  have hdescent : baseEnd_8012140 < baseStart_8012140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012196 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_8012196 : Nat := 118140960795 + 8012196 * 2 ^ 59
def prefixEnd_8012196 : Nat := 4983230072969 + 3 ^ 40 * 8012196 * 2
def baseEnd_8012196 : Nat := 1371369215343679826667529

theorem tailTrace_8012196 : CollatzResearch.WordTrace tailWord_8012196 prefixEnd_8012196 1371369215343679826667529 := by
  unfold tailWord_8012196
  simp only [CollatzResearch.WordTrace]
  refine ⟨146114397840594870490040221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194819197120793160653386961 146114397840594870490040221)
  ·
    refine ⟨54792899190223076433765083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146114397840594870490040221 54792899190223076433765083)
    ·
      refine ⟨82189348785334614650647625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54792899190223076433765083 82189348785334614650647625)
      ·
        refine ⟨61642011589000960987985719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82189348785334614650647625 61642011589000960987985719)
        ·
          refine ⟨92463017383501441481978579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61642011589000960987985719 92463017383501441481978579)
          ·
            refine ⟨138694526075252162222967869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92463017383501441481978579 138694526075252162222967869)
            ·
              refine ⟨52010447278219560833612951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138694526075252162222967869 52010447278219560833612951)
              ·
                refine ⟨78015670917329341250419427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52010447278219560833612951 78015670917329341250419427)
                ·
                  refine ⟨117023506375994011875629141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78015670917329341250419427 117023506375994011875629141)
                  ·
                    refine ⟨1371369215343679826667529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117023506375994011875629141 1371369215343679826667529)
                    ·
                      rfl

theorem cell23_8012196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_8012196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012196 prefixEnd_8012196 := by exact prefixLift 8012196
  have htrace : WordTrace (prefixWord ++ tailWord_8012196) baseStart_8012196 baseEnd_8012196 := by
    simpa [prefixWord, tailWord_8012196, baseEnd_8012196] using wordTrace_append hprefix tailTrace_8012196
  have hstable : (prefixWord ++ tailWord_8012196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012196).length < 2 ^ (prefixWord ++ tailWord_8012196).sum := by decide
  have hdescent : baseEnd_8012196 < baseStart_8012196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012216 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_8012216 : Nat := 118140960795 + 8012216 * 2 ^ 59
def prefixEnd_8012216 : Nat := 4983230072969 + 3 ^ 40 * 8012216 * 2
def baseEnd_8012216 : Nat := 4114117915644129401752495

theorem tailTrace_8012216 : CollatzResearch.WordTrace tailWord_8012216 prefixEnd_8012216 4114117915644129401752495 := by
  unfold tailWord_8012216
  simp only [CollatzResearch.WordTrace]
  refine ⟨146114762570558642197904251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194819683427411522930539001 146114762570558642197904251)
  ·
    refine ⟨219172143855837963296856377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146114762570558642197904251 219172143855837963296856377)
    ·
      refine ⟨164379107891878472472642283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219172143855837963296856377 164379107891878472472642283)
      ·
        refine ⟨246568661837817708708963425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164379107891878472472642283 246568661837817708708963425)
        ·
          refine ⟨184926496378363281531722569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246568661837817708708963425 184926496378363281531722569)
          ·
            refine ⟨138694872283772461148791927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184926496378363281531722569 138694872283772461148791927)
            ·
              refine ⟨208042308425658691723187891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138694872283772461148791927 208042308425658691723187891)
              ·
                refine ⟨312063462638488037584781837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208042308425658691723187891 312063462638488037584781837)
                ·
                  refine ⟨117023798489433014094293189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312063462638488037584781837 117023798489433014094293189)
                  ·
                    refine ⟨21941962216768690142679973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117023798489433014094293189 21941962216768690142679973)
                    ·
                      refine ⟨4114117915644129401752495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21941962216768690142679973 4114117915644129401752495)
                      ·
                        rfl

theorem cell23_8012216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_8012216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012216 prefixEnd_8012216 := by exact prefixLift 8012216
  have htrace : WordTrace (prefixWord ++ tailWord_8012216) baseStart_8012216 baseEnd_8012216 := by
    simpa [prefixWord, tailWord_8012216, baseEnd_8012216] using wordTrace_append hprefix tailTrace_8012216
  have hstable : (prefixWord ++ tailWord_8012216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012216).length < 2 ^ (prefixWord ++ tailWord_8012216).sum := by decide
  have hdescent : baseEnd_8012216 < baseStart_8012216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012256 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 3, 7]
def baseStart_8012256 : Nat := 118140960795 + 8012256 * 2 ^ 59
def prefixEnd_8012256 : Nat := 4983230072969 + 3 ^ 40 * 8012256 * 2
def baseEnd_8012256 : Nat := 1371379484956769748417437

theorem tailTrace_8012256 : CollatzResearch.WordTrace tailWord_8012256 prefixEnd_8012256 1371379484956769748417437 := by
  unfold tailWord_8012256
  simp only [CollatzResearch.WordTrace]
  refine ⟨146115492030486185613632311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194820656040648247484843081 146115492030486185613632311)
  ·
    refine ⟨219173238045729278420448467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146115492030486185613632311 219173238045729278420448467)
    ·
      refine ⟨328759857068593917630672701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219173238045729278420448467 328759857068593917630672701)
      ·
        refine ⟨123284946400722719111502263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328759857068593917630672701 123284946400722719111502263)
        ·
          refine ⟨184927419601084078667253395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123284946400722719111502263 184927419601084078667253395)
          ·
            refine ⟨277391129401626118000880093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184927419601084078667253395 277391129401626118000880093)
            ·
              refine ⟨104021673525609794250330035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277391129401626118000880093 104021673525609794250330035)
              ·
                refine ⟨156032510288414691375495053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104021673525609794250330035 156032510288414691375495053)
                ·
                  refine ⟨58512191358155509265810645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156032510288414691375495053 58512191358155509265810645)
                  ·
                    refine ⟨1371379484956769748417437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58512191358155509265810645 1371379484956769748417437)
                    ·
                      rfl

theorem cell23_8012256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_8012256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012256 prefixEnd_8012256 := by exact prefixLift 8012256
  have htrace : WordTrace (prefixWord ++ tailWord_8012256) baseStart_8012256 baseEnd_8012256 := by
    simpa [prefixWord, tailWord_8012256, baseEnd_8012256] using wordTrace_append hprefix tailTrace_8012256
  have hstable : (prefixWord ++ tailWord_8012256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012256).length < 2 ^ (prefixWord ++ tailWord_8012256).sum := by decide
  have hdescent : baseEnd_8012256 < baseStart_8012256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012273 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 2, 5]
def baseStart_8012273 : Nat := 118140960795 + 8012273 * 2 ^ 59
def prefixEnd_8012273 : Nat := 4983230072969 + 3 ^ 40 * 8012273 * 2
def baseEnd_8012273 : Nat := 1371382394680478559579911

theorem tailTrace_8012273 : CollatzResearch.WordTrace tailWord_8012273 prefixEnd_8012273 1371382394680478559579911 := by
  unfold tailWord_8012273
  simp only [CollatzResearch.WordTrace]
  refine ⟨292231604101910783130633473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194821069401273855420422315 292231604101910783130633473)
  ·
    refine ⟨219173703076433087347975105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292231604101910783130633473 219173703076433087347975105)
    ·
      refine ⟨164380277307324815510981329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219173703076433087347975105 164380277307324815510981329)
      ·
        refine ⟨123285207980493611633235997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164380277307324815510981329 123285207980493611633235997)
        ·
          refine ⟨46231952992685104362463499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123285207980493611633235997 46231952992685104362463499)
          ·
            refine ⟨69347929489027656543695249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46231952992685104362463499 69347929489027656543695249)
            ·
              refine ⟨52010947116770742407771437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69347929489027656543695249 52010947116770742407771437)
              ·
                refine ⟨19504105168789028402914289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52010947116770742407771437 19504105168789028402914289)
                ·
                  refine ⟨14628078876591771302185717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19504105168789028402914289 14628078876591771302185717)
                  ·
                    refine ⟨1371382394680478559579911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14628078876591771302185717 1371382394680478559579911)
                    ·
                      rfl

theorem cell23_8012273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_8012273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012273 prefixEnd_8012273 := by exact prefixLift 8012273
  have htrace : WordTrace (prefixWord ++ tailWord_8012273) baseStart_8012273 baseEnd_8012273 := by
    simpa [prefixWord, tailWord_8012273, baseEnd_8012273] using wordTrace_append hprefix tailTrace_8012273
  have hstable : (prefixWord ++ tailWord_8012273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012273).length < 2 ^ (prefixWord ++ tailWord_8012273).sum := by decide
  have hdescent : baseEnd_8012273 < baseStart_8012273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012293 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_8012293 : Nat := 118140960795 + 8012293 * 2 ^ 59
def prefixEnd_8012293 : Nat := 4983230072969 + 3 ^ 40 * 8012293 * 2
def baseEnd_8012293 : Nat := 4114157453654525600489641

theorem tailTrace_8012293 : CollatzResearch.WordTrace tailWord_8012293 prefixEnd_8012293 4114157453654525600489641 := by
  unfold tailWord_8012293
  simp only [CollatzResearch.WordTrace]
  refine ⟨292232333561838326546361533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194821555707892217697574355 292232333561838326546361533)
  ·
    refine ⟨109587125085689372454885575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 292232333561838326546361533 109587125085689372454885575)
    ·
      refine ⟨164380687628534058682328363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109587125085689372454885575 164380687628534058682328363)
      ·
        refine ⟨246571031442801088023492545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164380687628534058682328363 246571031442801088023492545)
        ·
          refine ⟨184928273582100816017619409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246571031442801088023492545 184928273582100816017619409)
          ·
            refine ⟨138696205186575612013214557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184928273582100816017619409 138696205186575612013214557)
            ·
              refine ⟨52011076944965854504955459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138696205186575612013214557 52011076944965854504955459)
              ·
                refine ⟨78016615417448781757433189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52011076944965854504955459 78016615417448781757433189)
                ·
                  refine ⟨14628115390771646579518723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78016615417448781757433189 14628115390771646579518723)
                  ·
                    refine ⟨21942173086157469869278085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14628115390771646579518723 21942173086157469869278085)
                    ·
                      refine ⟨4114157453654525600489641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21942173086157469869278085 4114157453654525600489641)
                      ·
                        rfl

theorem cell23_8012293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_8012293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012293 prefixEnd_8012293 := by exact prefixLift 8012293
  have htrace : WordTrace (prefixWord ++ tailWord_8012293) baseStart_8012293 baseEnd_8012293 := by
    simpa [prefixWord, tailWord_8012293, baseEnd_8012293] using wordTrace_append hprefix tailTrace_8012293
  have hstable : (prefixWord ++ tailWord_8012293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012293).length < 2 ^ (prefixWord ++ tailWord_8012293).sum := by decide
  have hdescent : baseEnd_8012293 < baseStart_8012293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012294 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_8012294 : Nat := 118140960795 + 8012294 * 2 ^ 59
def prefixEnd_8012294 : Nat := 4983230072969 + 3 ^ 40 * 8012294 * 2
def baseEnd_8012294 : Nat := 457128663015020010730793

theorem tailTrace_8012294 : CollatzResearch.WordTrace tailWord_8012294 prefixEnd_8012294 457128663015020010730793 := by
  unfold tailWord_8012294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132261563588584491160873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 194821580023223135811431957 9132261563588584491160873)
  ·
    refine ⟨6849196172691438368370655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9132261563588584491160873 6849196172691438368370655)
    ·
      refine ⟨10273794259037157552555983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6849196172691438368370655 10273794259037157552555983)
      ·
        refine ⟨15410691388555736328833975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10273794259037157552555983 15410691388555736328833975)
        ·
          refine ⟨23116037082833604493250963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15410691388555736328833975 23116037082833604493250963)
          ·
            refine ⟨34674055624250406739876445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23116037082833604493250963 34674055624250406739876445)
            ·
              refine ⟨13002770859093902527453667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34674055624250406739876445 13002770859093902527453667)
              ·
                refine ⟨19504156288640853791180501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13002770859093902527453667 19504156288640853791180501)
                ·
                  refine ⟨457128663015020010730793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19504156288640853791180501 457128663015020010730793)
                  ·
                    rfl

theorem cell23_8012294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_8012294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012294 prefixEnd_8012294 := by exact prefixLift 8012294
  have htrace : WordTrace (prefixWord ++ tailWord_8012294) baseStart_8012294 baseEnd_8012294 := by
    simpa [prefixWord, tailWord_8012294, baseEnd_8012294] using wordTrace_append hprefix tailTrace_8012294
  have hstable : (prefixWord ++ tailWord_8012294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012294).length < 2 ^ (prefixWord ++ tailWord_8012294).sum := by decide
  have hdescent : baseEnd_8012294 < baseStart_8012294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012360 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_8012360 : Nat := 118140960795 + 8012360 * 2 ^ 59
def prefixEnd_8012360 : Nat := 4983230072969 + 3 ^ 40 * 8012360 * 2
def baseEnd_8012360 : Nat := 4114191856858376838351833

theorem tailTrace_8012360 : CollatzResearch.WordTrace tailWord_8012360 prefixEnd_8012360 4114191856858376838351833 := by
  unfold tailWord_8012360
  simp only [CollatzResearch.WordTrace]
  refine ⟨146117388626297798494525267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194823184835063731326033689 146117388626297798494525267)
  ·
    refine ⟨219176082939446697741787901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146117388626297798494525267 219176082939446697741787901)
    ·
      refine ⟨82191031102292511653170463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219176082939446697741787901 82191031102292511653170463)
      ·
        refine ⟨123286546653438767479755695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82191031102292511653170463 123286546653438767479755695)
        ·
          refine ⟨184929819980158151219633543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123286546653438767479755695 184929819980158151219633543)
          ·
            refine ⟨277394729970237226829450315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184929819980158151219633543 277394729970237226829450315)
            ·
              refine ⟨416092094955355840244175473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277394729970237226829450315 416092094955355840244175473)
              ·
                refine ⟨312069071216516880183131605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416092094955355840244175473 312069071216516880183131605)
                ·
                  refine ⟨7314118856637114379292147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 312069071216516880183131605 7314118856637114379292147)
                  ·
                    refine ⟨10971178284955671568938221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7314118856637114379292147 10971178284955671568938221)
                    ·
                      refine ⟨4114191856858376838351833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10971178284955671568938221 4114191856858376838351833)
                      ·
                        rfl

theorem cell23_8012360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_8012360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012360 prefixEnd_8012360 := by exact prefixLift 8012360
  have htrace : WordTrace (prefixWord ++ tailWord_8012360) baseStart_8012360 baseEnd_8012360 := by
    simpa [prefixWord, tailWord_8012360, baseEnd_8012360] using wordTrace_append hprefix tailTrace_8012360
  have hstable : (prefixWord ++ tailWord_8012360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012360).length < 2 ^ (prefixWord ++ tailWord_8012360).sum := by decide
  have hdescent : baseEnd_8012360 < baseStart_8012360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012363 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 3, 5]
def baseStart_8012363 : Nat := 118140960795 + 8012363 * 2 ^ 59
def prefixEnd_8012363 : Nat := 4983230072969 + 3 ^ 40 * 8012363 * 2
def baseEnd_8012363 : Nat := 1371397799100113442204773

theorem tailTrace_8012363 : CollatzResearch.WordTrace tailWord_8012363 prefixEnd_8012363 1371397799100113442204773 := by
  unfold tailWord_8012363
  simp only [CollatzResearch.WordTrace]
  refine ⟨292234886671584728501409743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194823257781056485667606495 292234886671584728501409743)
  ·
    refine ⟨438352330007377092752114615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292234886671584728501409743 438352330007377092752114615)
    ·
      refine ⟨657528495011065639128171923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438352330007377092752114615 657528495011065639128171923)
      ·
        refine ⟨986292742516598458692257885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657528495011065639128171923 986292742516598458692257885)
        ·
          refine ⟨369859778443724422009596707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 986292742516598458692257885 369859778443724422009596707)
          ·
            refine ⟨554789667665586633014395061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369859778443724422009596707 554789667665586633014395061)
            ·
              refine ⟨52011531343648746845099537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 554789667665586633014395061 52011531343648746845099537)
              ·
                refine ⟨39008648507736560133824653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52011531343648746845099537 39008648507736560133824653)
                ·
                  refine ⟨14628243190401210050184245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39008648507736560133824653 14628243190401210050184245)
                  ·
                    refine ⟨1371397799100113442204773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14628243190401210050184245 1371397799100113442204773)
                    ·
                      rfl

theorem cell23_8012363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 5].length) (baseStart_8012363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012363 prefixEnd_8012363 := by exact prefixLift 8012363
  have htrace : WordTrace (prefixWord ++ tailWord_8012363) baseStart_8012363 baseEnd_8012363 := by
    simpa [prefixWord, tailWord_8012363, baseEnd_8012363] using wordTrace_append hprefix tailTrace_8012363
  have hstable : (prefixWord ++ tailWord_8012363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012363).length < 2 ^ (prefixWord ++ tailWord_8012363).sum := by decide
  have hdescent : baseEnd_8012363 < baseStart_8012363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012397 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_8012397 : Nat := 118140960795 + 8012397 * 2 ^ 59
def prefixEnd_8012397 : Nat := 4983230072969 + 3 ^ 40 * 8012397 * 2
def baseEnd_8012397 : Nat := 1371403618547531064529721

theorem tailTrace_8012397 : CollatzResearch.WordTrace tailWord_8012397 prefixEnd_8012397 1371403618547531064529721 := by
  unfold tailWord_8012397
  simp only [CollatzResearch.WordTrace]
  refine ⟨292236126753461552308147445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194824084502307701538764963 292236126753461552308147445)
  ·
    refine ⟨27397136883137020528888823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 292236126753461552308147445 27397136883137020528888823)
    ·
      refine ⟨41095705324705530793333235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27397136883137020528888823 41095705324705530793333235)
      ·
        refine ⟨61643557987058296189999853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41095705324705530793333235 61643557987058296189999853)
        ·
          refine ⟨23116334245146861071249945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61643557987058296189999853 23116334245146861071249945)
          ·
            refine ⟨17337250683860145803437459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23116334245146861071249945 17337250683860145803437459)
            ·
              refine ⟨26005876025790218705156189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17337250683860145803437459 26005876025790218705156189)
              ·
                refine ⟨9752203509671332014433571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26005876025790218705156189 9752203509671332014433571)
                ·
                  refine ⟨14628305264506998021650357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9752203509671332014433571 14628305264506998021650357)
                  ·
                    refine ⟨1371403618547531064529721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14628305264506998021650357 1371403618547531064529721)
                    ·
                      rfl

theorem cell23_8012397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_8012397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012397 prefixEnd_8012397 := by exact prefixLift 8012397
  have htrace : WordTrace (prefixWord ++ tailWord_8012397) baseStart_8012397 baseEnd_8012397 := by
    simpa [prefixWord, tailWord_8012397, baseEnd_8012397] using wordTrace_append hprefix tailTrace_8012397
  have hstable : (prefixWord ++ tailWord_8012397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012397).length < 2 ^ (prefixWord ++ tailWord_8012397).sum := by decide
  have hdescent : baseEnd_8012397 < baseStart_8012397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012418 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 6]
def baseStart_8012418 : Nat := 118140960795 + 8012418 * 2 ^ 59
def prefixEnd_8012418 : Nat := 4983230072969 + 3 ^ 40 * 8012418 * 2
def baseEnd_8012418 : Nat := 457135737637370845714063

theorem tailTrace_8012418 : CollatzResearch.WordTrace tailWord_8012418 prefixEnd_8012418 457135737637370845714063 := by
  unfold tailWord_8012418
  simp only [CollatzResearch.WordTrace]
  refine ⟨73059223171596368223665477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 194824595124256981929774605 73059223171596368223665477)
  ·
    refine ⟨13698604344674319041937277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73059223171596368223665477 13698604344674319041937277)
    ·
      refine ⟨5136976629252869640726479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13698604344674319041937277 5136976629252869640726479)
      ·
        refine ⟨7705464943879304461089719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5136976629252869640726479 7705464943879304461089719)
        ·
          refine ⟨11558197415818956691634579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7705464943879304461089719 11558197415818956691634579)
          ·
            refine ⟨17337296123728435037451869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11558197415818956691634579 17337296123728435037451869)
            ·
              refine ⟨6501486046398163139044451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17337296123728435037451869 6501486046398163139044451)
              ·
                refine ⟨9752229069597244708566677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501486046398163139044451 9752229069597244708566677)
                ·
                  refine ⟨457135737637370845714063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9752229069597244708566677 457135737637370845714063)
                  ·
                    rfl

theorem cell23_8012418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_8012418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012418 prefixEnd_8012418 := by exact prefixLift 8012418
  have htrace : WordTrace (prefixWord ++ tailWord_8012418) baseStart_8012418 baseEnd_8012418 := by
    simpa [prefixWord, tailWord_8012418, baseEnd_8012418] using wordTrace_append hprefix tailTrace_8012418
  have hstable : (prefixWord ++ tailWord_8012418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012418).length < 2 ^ (prefixWord ++ tailWord_8012418).sum := by decide
  have hdescent : baseEnd_8012418 < baseStart_8012418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012420 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_8012420 : Nat := 118140960795 + 8012420 * 2 ^ 59
def prefixEnd_8012420 : Nat := 4983230072969 + 3 ^ 40 * 8012420 * 2
def baseEnd_8012420 : Nat := 4114222665697646603601557

theorem tailTrace_8012420 : CollatzResearch.WordTrace tailWord_8012420 prefixEnd_8012420 4114222665697646603601557 := by
  unfold tailWord_8012420
  simp only [CollatzResearch.WordTrace]
  refine ⟨146118482816189113618117357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194824643754918818157489809 146118482816189113618117357)
  ·
    refine ⟨54794431056070917606794009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146118482816189113618117357 54794431056070917606794009)
    ·
      refine ⟨41095823292053188205095507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54794431056070917606794009 41095823292053188205095507)
      ·
        refine ⟨61643734938079782307643261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41095823292053188205095507 61643734938079782307643261)
        ·
          refine ⟨23116400601779918365366223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61643734938079782307643261 23116400601779918365366223)
          ·
            refine ⟨34674600902669877548049335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23116400601779918365366223 34674600902669877548049335)
            ·
              refine ⟨52011901354004816322074003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34674600902669877548049335 52011901354004816322074003)
              ·
                refine ⟨78017852031007224483111005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52011901354004816322074003 78017852031007224483111005)
                ·
                  refine ⟨29256694511627709181166627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78017852031007224483111005 29256694511627709181166627)
                  ·
                    refine ⟨43885041767441563771749941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29256694511627709181166627 43885041767441563771749941)
                    ·
                      refine ⟨4114222665697646603601557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43885041767441563771749941 4114222665697646603601557)
                      ·
                        rfl

theorem cell23_8012420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_8012420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8012420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8012420 prefixEnd_8012420 := by exact prefixLift 8012420
  have htrace : WordTrace (prefixWord ++ tailWord_8012420) baseStart_8012420 baseEnd_8012420 := by
    simpa [prefixWord, tailWord_8012420, baseEnd_8012420] using wordTrace_append hprefix tailTrace_8012420
  have hstable : (prefixWord ++ tailWord_8012420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012420).length < 2 ^ (prefixWord ++ tailWord_8012420).sum := by decide
  have hdescent : baseEnd_8012420 < baseStart_8012420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
